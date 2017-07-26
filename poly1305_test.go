// Copyright (c) 2016 Andreas Auernhammer. All rights reserved.
// Use of this source code is governed by a license that can be
// found in the LICENSE file.

package poly1305

import (
	"bytes"
	"encoding/hex"
	"testing"
	"github.com/minio/blake2b-simd"
	"github.com/aead/siphash"
	"sort"
	"time"
	"fmt"
	"math/big"
	"math/rand"
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
	return byte(((1 << s)-1) << uint(b % m))
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

func testQuality(t *testing.T, key [32]byte, shift uint, algo string) {
	start := time.Now()

	msg := make([]byte, 1<<shift)
	for i := range msg {
		msg[i] = byte(i)
	}

	var keys []string

	for m := 8; m >= 1; m-- {
		for b := 0; b < len(msg)*m; b++ {
			// Change message with mask
			msg[b / m] = msg[b / m] ^ mask(b, m)

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
			tagstr := hex.EncodeToString(tag[:])

			keys = append(keys, tagstr)
			// Undo change
			msg[b / m] = msg[b / m] ^ mask(b, m)
		}
	}

	// sanity check if message not corrupted
	for i := range msg {
		if msg[i] != byte(i) {
			panic("memory corrupted")
		}
	}

	sort.Strings(keys)

	var tagprev *big.Int
	var smallest *big.Int

	for i, k := range keys {

		tag := new(big.Int)
		tag.SetString(k, 16)

		if i > 0 {
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
	}

	elapsed := time.Since(start)
	fmt.Println(smallest)
	fmt.Printf("Permutations: %d -- equal bits: %d -- duration: %v (%s)\n", len(keys), 4*len(keys[1])-len(smallest.Text(2)), elapsed, algo)
}

func TestQuality(t *testing.T) {

	rand.Seed(time.Now().UTC().UnixNano())

	var key [32]byte
	for i := range key {
		key[i] = byte(255-i) // byte(rand.Intn(256)) //
	}

	algo := ""
	//algo = "blake2b"
	//algo = "poly1305"
	algo = "siphash"
	for shift := uint(8); shift < 14; shift++ {

		testQuality(t, key, shift, algo)
	}
}

// XOR single bit
// Permutations:     512  (5) -- equal bits: 17
// Permutations:    1024  (6) -- equal bits: 19
// Permutations:    2048  (7) -- equal bits: 22
// Permutations:    4096  (8) -- equal bits: 23
// Permutations:    8192  (9) -- equal bits: 26
// Permutations:   16384 (10) -- equal bits: 29
// Permutations:   32768 (11) -- equal bits: 29
// Permutations:   65536 (12) -- equal bits: 30
// Permutations:  131072 (13) -- equal bits: 34
// Permutations:  262144 (14) -- equal bits: 36
// Permutations:  524288 (15) -- equal bits: 37
// Permutations: 1048576 (16) -- equal bits: 38
// Permutations: 2097152 (17) -- equal bits: 42

// XOR multiple bits
// Permutations:     288  (2) -- equal bits: 23
// Permutations:     576  (3) -- equal bits: 20
// Permutations:    1152  (4) -- equal bits: 25
// Permutations:    2304  (5) -- equal bits: 20
// Permutations:    4608  (6) -- equal bits: 22
// Permutations:    9216  (7) -- equal bits: 28
// Permutations:   18432  (8) -- equal bits: 31
// Permutations:   36864  (9) -- equal bits: 31
// Permutations:   73728 (10) -- equal bits: 33
// Permutations:  147456 (11) -- equal bits: 33
// Permutations:  294912 (12) -- equal bits: 38
// Permutations:  589824 (13) -- equal bits: 40
// Permutations: 1179648 (14) -- equal bits: 40
// Permutations: 2359296 (15) -- equal bits: 41
// Permutations: 4718592 (16) -- equal bits: 45

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
