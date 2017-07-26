// Copyright (c) 2016 Andreas Auernhammer. All rights reserved.
// Use of this source code is governed by a license that can be
// found in the LICENSE file.

package poly1305

import (
	"bytes"
	"container/heap"
	"encoding/hex"
	"fmt"
	"github.com/aead/siphash"
	"github.com/minio/blake2b-simd"
	"math/big"
	"math/rand"
	"runtime"
	"sort"
	"strconv"
	"sync"
	"testing"
	"time"
)

func fromHex(s string) []byte {
	b, err := hex.DecodeString(s)
	if err != nil {
		panic(err)
	}
	return b
}

var vectors = []struct {
	msg, key, tag []byte
}{
	{
		[]byte("Hello world!"),
		[]byte("this is 32-byte key for Poly1305"),
		[]byte{0xa6, 0xf7, 0x45, 0x00, 0x8f, 0x81, 0xc9, 0x16, 0xa2, 0x0d, 0xcc, 0x74, 0xee, 0xf2, 0xb2, 0xf0},
	},
	{
		make([]byte, 32),
		[]byte("this is 32-byte key for Poly1305"),
		[]byte{0x49, 0xec, 0x78, 0x09, 0x0e, 0x48, 0x1e, 0xc6, 0xc2, 0x6b, 0x33, 0xb9, 0x1c, 0xcc, 0x03, 0x07},
	},
	{
		make([]byte, 2007),
		[]byte("this is 32-byte key for Poly1305"),
		[]byte{0xda, 0x84, 0xbc, 0xab, 0x02, 0x67, 0x6c, 0x38, 0xcd, 0xb0, 0x15, 0x60, 0x42, 0x74, 0xc2, 0xaa},
	},
	{
		make([]byte, 2007),
		make([]byte, 32),
		make([]byte, 16),
	},
	{
		// This test triggers an edge-case. See https://go-review.googlesource.com/#/c/30101/.
		[]byte{0x81, 0xd8, 0xb2, 0xe4, 0x6a, 0x25, 0x21, 0x3b, 0x58, 0xfe, 0xe4, 0x21, 0x3a, 0x2a, 0x28, 0xe9, 0x21, 0xc1, 0x2a, 0x96, 0x32, 0x51, 0x6d, 0x3b, 0x73, 0x27, 0x27, 0x27, 0xbe, 0xcf, 0x21, 0x29},
		[]byte{0x3b, 0x3a, 0x29, 0xe9, 0x3b, 0x21, 0x3a, 0x5c, 0x5c, 0x3b, 0x3b, 0x05, 0x3a, 0x3a, 0x8c, 0x0d},
		[]byte{0x6d, 0xc1, 0x8b, 0x8c, 0x34, 0x4c, 0xd7, 0x99, 0x27, 0x11, 0x8b, 0xbe, 0x84, 0xb7, 0xf3, 0x14},
	},
	// From: https://tools.ietf.org/html/rfc7539#section-2.5.2
	{
		fromHex("43727970746f6772617068696320466f72756d2052657365617263682047726f7570"),
		fromHex("85d6be7857556d337f4452fe42d506a80103808afb0db2fd4abff6af4149f51b"),
		fromHex("a8061dc1305136c6c22b8baf0c0127a9"),
	},
}

func TestVectors(t *testing.T) {
	var key [32]byte

	for i, v := range vectors {
		msg := v.msg
		copy(key[:], v.key)

		out := Sum(msg, key)
		if !bytes.Equal(out[:], v.tag) {
			t.Errorf("Test vector %d : got: %x expected: %x", i, out[:], v.tag)
		}

		h := New(key)
		h.Write(msg)
		tag := h.Sum(nil)
		if !bytes.Equal(tag[:], v.tag) {
			t.Errorf("Test vector %d : got: %x expected: %x", i, tag[:], v.tag)
		}

		var mac [16]byte
		copy(mac[:], v.tag)
		if !Verify(&mac, msg, key) {
			t.Errorf("Test vector %d : Verify failed", i)
		}
	}
}

func TestWriteAfterSum(t *testing.T) {
	msg := make([]byte, 64)
	for i := range msg {
		h := New([32]byte{})

		if _, err := h.Write(msg[:i]); err != nil {
			t.Fatalf("Iteration %d: poly1305.Hash returned unexpected error: %s", i, err)
		}
		h.Sum(nil)
		if _, err := h.Write(nil); err == nil {
			t.Fatalf("Iteration %d: poly1305.Hash returned no error for write after sum", i)
		}
	}
}

func testWrite(t *testing.T, size int) {
	var key [32]byte
	for i := range key {
		key[i] = byte(i)
	}

	h := New(key)

	var msg1 []byte
	msg0 := make([]byte, size)
	for i := range msg0 {
		h.Write(msg0[:i])
		msg1 = append(msg1, msg0[:i]...)
	}

	tag0 := h.Sum(nil)
	tag1 := Sum(msg1, key)

	if !bytes.Equal(tag0[:], tag1[:]) {
		t.Fatalf("Sum differ from poly1305.Sum\n Sum: %s \n poly1305.Sum: %s", hex.EncodeToString(tag0[:]), hex.EncodeToString(tag1[:]))
	}
}

func TestWrite(t *testing.T) {

	for size := 0; size < 128; size++ {
		testWrite(t, size)
	}
}

func mask(b, m int) byte {
	s := uint(9 - m)
	return byte(((1 << s) - 1) << uint(b%m))
}

func Blake2bSum(buf []byte) []byte {
	h := blake2b.New512()
	h.Reset()
	h.Write(buf[:])
	sum := h.Sum(nil)
	return sum
}

func SipHashSum(buf []byte, key [32]byte) []byte {
	h, _ := siphash.New128(key[0:16])
	h.Reset()
	h.Write(buf[:])
	sum := h.Sum(nil)
	return sum
}

func testQualitySubset(msg []byte, key [32]byte, cpu int, cpuShift uint, algo string, results chan<- sortBytes) {

	var keys sortBytes

	for m := 8; m >= 1; m-- {

		bStart := (len(msg) * m * cpu) >> cpuShift
		bEnd := (len(msg) * m * (cpu + 1)) >> cpuShift

		for b := bStart; b < bEnd; b++ {
			// Change message with mask
			msg[b/m] = msg[b/m] ^ mask(b, m)

			var tag []byte
			switch algo {
			case "poly1305":
				tag = make([]byte, 16)
				t := Sum(msg, key)
				copy(tag, t[:])
			case "blake2b":
				tag = Blake2bSum(msg)
			case "siphash":
				tag = SipHashSum(msg, key)
			}

			keys = append(keys, tag)
			// Undo change
			msg[b/m] = msg[b/m] ^ mask(b, m)
		}
	}

	// sanity check if message not corrupted
	for i := range msg {
		if msg[i] != byte(i) {
			panic("memory corrupted")
		}
	}

	sort.Sort(keys)

	results <- keys
}

func testQuality(t *testing.T, key [32]byte, shift uint, algo string) {
	start := time.Now()

	msg := make([]byte, 1<<shift)
	for i := range msg {
		msg[i] = byte(i)
	}

	cpus := runtime.NumCPU()
	// make sure nr of CPUs is a power of 2
	cpuShift := uint(len(strconv.FormatInt(int64(cpus), 2)) - 1)
	cpus = 1 << cpuShift

	var wg sync.WaitGroup
	results := make(chan sortBytes)

	for cpu := 0; cpu < cpus; cpu++ {

		wg.Add(1)
		go func(cpu int) {
			msgCopy := make([]byte, len(msg))
			copy(msgCopy, msg)
			defer wg.Done()
			testQualitySubset(msgCopy, key, cpu, cpuShift, algo, results)
		}(cpu)
	}

	// Wait for workers to complete
	go func() {
		wg.Wait()
		close(results) // Close output channel
	}()

	keys := make([]sortBytes, 0, cpus)

	// Collect sub sorts
	for r := range results {
		keys = append(keys, r)
	}

	var tagprev *big.Int
	var smallest *big.Int

	h := &HexHeap{}
	heap.Init(h)

	// Push initial keys onto heap
	for stack, sb := range keys {
		if len(sb) > 0 {
			heap.Push(h, Hex{hex.EncodeToString(sb[0]), stack, 1})
		}
	}

	// Iterate over heap
	for h.Len() > 0 {
		hi := heap.Pop(h).(Hex)

		tag := new(big.Int)
		tag.SetString(hi.hex, 16)

		if tagprev != nil {
			diff := new(big.Int)
			diff.Sub(tag, tagprev)
			//fmt.Println(k, diff)

			if smallest == nil {
				smallest = new(big.Int)
				*smallest = *diff
			} else if smallest.Cmp(diff) > 0 {
				*smallest = *diff
			}
		}

		tagprev = tag

		if hi.index < len(keys[hi.stack]) { // Push new entry when still available
			heap.Push(h, Hex{hex.EncodeToString(keys[hi.stack][hi.index]), hi.stack, hi.index + 1})
		}
	}

	elapsed := time.Since(start)
	fmt.Println(smallest)
	fmt.Printf("Permutations: %d -- equal bits: %d -- duration: %v (%s)\n", len(keys[0]), 8*len(keys[0][0])-len(smallest.Text(2)), elapsed, algo)
}

// An HexHeap is a min-heap of hexadecimals.
type HexHeap []Hex

type Hex struct {
	hex   string
	stack int
	index int
}

func (h HexHeap) Len() int           { return len(h) }
func (h HexHeap) Less(i, j int) bool { return h[i].hex < h[j].hex }
func (h HexHeap) Swap(i, j int)      { h[i], h[j] = h[j], h[i] }

func (h *HexHeap) Push(x interface{}) {
	*h = append(*h, x.(Hex))
}

func (h *HexHeap) Pop() interface{} {
	old := *h
	n := len(old)
	x := old[n-1]
	*h = old[0 : n-1]
	return x
}

// Slice of sorted bytes
type sortBytes [][]byte

func (s sortBytes) Less(i, j int) bool {
	for index := range s[i] {
		if s[i][index] != s[j][index] {
			return s[i][index] < s[j][index]
		}
	}
	return false
}

func (s sortBytes) Swap(i, j int) {
	s[i], s[j] = s[j], s[i]
}

func (s sortBytes) Len() int {
	return len(s)
}

func TestQuality(t *testing.T) {

	rand.Seed(time.Now().UTC().UnixNano())

	var key [32]byte
	for i := range key {
		key[i] = byte(255 - i) // byte(rand.Intn(256))
	}

	algo := ""
	//algo = "blake2b"
	//algo = "poly1305"
	algo = "siphash"
	for shift := uint(8); shift < 16; shift++ {

		testQuality(t, key, shift, algo)
	}
}

// Benchmarks

func BenchmarkSum_64(b *testing.B)    { benchmarkSum(b, 64) }
func BenchmarkSum_256(b *testing.B)   { benchmarkSum(b, 256) }
func BenchmarkSum_1K(b *testing.B)    { benchmarkSum(b, 1024) }
func BenchmarkSum_8K(b *testing.B)    { benchmarkSum(b, 8*1024) }
func BenchmarkWrite_64(b *testing.B)  { benchmarkWrite(b, 64) }
func BenchmarkWrite_256(b *testing.B) { benchmarkWrite(b, 256) }
func BenchmarkWrite_1K(b *testing.B)  { benchmarkWrite(b, 1024) }
func BenchmarkWrite_8K(b *testing.B)  { benchmarkWrite(b, 8*1024) }

func benchmarkSum(b *testing.B, size int) {
	var key [32]byte

	msg := make([]byte, size)

	b.SetBytes(int64(size))
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		Sum(msg, key)
	}
}

func benchmarkWrite(b *testing.B, size int) {
	var key [32]byte
	h := New(key)

	msg := make([]byte, size)

	b.SetBytes(int64(size))
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		h.Write(msg)
	}
}
