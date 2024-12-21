package ownsm3

import (
	"encoding/binary"
	"hash"
)

// Size the size of a SM3 checksum in bytes.
const Size = 32

// SizeBitSize the bit size of Size.
const SizeBitSize = 5

// BlockSize the blocksize of SM3 in bytes.
const BlockSize = 64

var IV = [8]uint32{
	0x7380166F, 0x4914B2B9, 0x172442D7, 0xDA8A0600,
	0xA96F30BC, 0x163138AA, 0xE38DEE4D, 0xB0FB0E4E,
}

var T_j_le_15 uint32 = 0x79cc4519
var T_j_gt_15 uint32 = 0x7a879d8a

func T(j int) uint32 {
	if j >= 0 && j <= 15 {
		return 0x79cc4519
	}
	if j >= 16 && j <= 63 {
		return 0x7a879d8a
	}
	panic("Panic in func T\n")
}

func FF(x uint32, y uint32, z uint32, j int) uint32 {
	if j >= 0 && j <= 15 {
		return x ^ y ^ z
	}

	return (x & y) | (x & z) | (y & z)
}

func GG(x uint32, y uint32, z uint32, j int) uint32 {
	if j < 16 {
		return x ^ y ^ z
	}
	return (x & y) | ((^x) & z)
}

func Rotate_Left_Shift(x uint32, count int) uint32 {
	count = count % 32
	return (x << count) | (x >> (32 - count))
}

func P0(x uint32) uint32 {
	return x ^ Rotate_Left_Shift(x, 9) ^ Rotate_Left_Shift(x, 17)
}

func P1(x uint32) uint32 {
	return x ^ Rotate_Left_Shift(x, 15) ^ Rotate_Left_Shift(x, 23)
}

func pad_message(message []byte) []byte {
	message_len := len(message) * 8
	remain_len := message_len % 512
	var k int

	if remain_len+1 <= 448 {
		k = 447 - remain_len
	} else {
		k = 959 - remain_len
	}

	k++
	padding_byte_len := k / 8

	// fmt.Printf("%d\n%d\n", k, padding_byte_len)

	if k%8 != 0 || padding_byte_len == 0 {
		panic("Panic in func padding\n")
	}

	message = append(message, 0x80)
	for i := 1; i < padding_byte_len; i++ {
		message = append(message, 0x00)
	}

	lengthBytes := make([]byte, 8)
	binary.BigEndian.PutUint64(lengthBytes, uint64(message_len))
	message = append(message, lengthBytes...)

	return message
}

// extend_message is the message expansion function for SM3.
func extend_message(block []byte) ([68]uint32, [64]uint32) {
	var W_1st [68]uint32
	var W_2nd [64]uint32

	for i := 0; i <= 15; i++ {
		W_1st[i] = binary.BigEndian.Uint32(block[i*4 : (i+1)*4])
	}

	for j := 16; j <= 67; j++ {
		W_1st[j] = P1(W_1st[j-16]^W_1st[j-9]^Rotate_Left_Shift(W_1st[j-3], 15)) ^
			Rotate_Left_Shift(W_1st[j-13], 7) ^ W_1st[j-6]
	}

	for j := 0; j <= 63; j++ {
		W_2nd[j] = W_1st[j] ^ W_1st[j+4]
	}

	return W_1st, W_2nd
}

type digest struct {
	h   [8]uint32
	x   [64]byte
	nx  int
	len uint64
}

// New creates and returns a new instance of digest, which implements the hash.Hash interface.
func New() hash.Hash {
	d := new(digest)
	d.Reset()
	return d
}

func (d *digest) Reset() {
	d.h = IV
	d.nx = 0
	d.len = 0
}

func (d *digest) Size() int {
	return 32 // SM3 hash size in bytes
}

func (d *digest) BlockSize() int {
	return 64
}

func (d *digest) processBlock(block []byte) {
	W_1st, W_2nd := extend_message(block)

	A, B, C, D, E, F, G, H := d.h[0], d.h[1], d.h[2], d.h[3], d.h[4], d.h[5], d.h[6], d.h[7]

	for j := 0; j < 64; j++ {
		SS1 := Rotate_Left_Shift((Rotate_Left_Shift(A, 12) + E + Rotate_Left_Shift(T(j), j)), 7)
		SS2 := SS1 ^ Rotate_Left_Shift(A, 12)
		TT1 := FF(A, B, C, j) + D + SS2 + W_2nd[j]
		TT2 := GG(E, F, G, j) + H + SS1 + W_1st[j]
		D = C
		C = Rotate_Left_Shift(B, 9)
		B = A
		A = TT1
		H = G
		G = Rotate_Left_Shift(F, 19)
		F = E
		E = P0(TT2)
	}

	// Update hash state
	for i := 0; i < 8; i++ {
		d.h[i] ^= [8]uint32{A, B, C, D, E, F, G, H}[i]
	}
}

func (d *digest) Write(p []byte) (n int, err error) {
	n = len(p)
	d.len += uint64(n)
	if d.nx > 0 {
		// Handle leftover data from previous block
		remaining := copy(d.x[d.nx:], p)
		d.nx += remaining
		if d.nx == 64 {
			// Process a full 64-byte block
			d.processBlock(d.x[:])
			d.nx = 0
		}
		p = p[remaining:]
	}
	// Process full 64-byte blocks
	for len(p) >= 64 {
		d.processBlock(p[:64])
		p = p[64:]
	}
	// Handle remaining data that doesn't fill a full block
	if len(p) > 0 {
		d.nx = copy(d.x[:], p)
	}
	return
}

func (d *digest) Sum(in []byte) []byte {
	// Make a copy of d so that caller can keep writing and summing.
	d0 := *d
	total_len := d0.len * 8
	remain_len := total_len % 512
	d0.x[d0.nx] = 0x80
	d0.nx++

	if d0.nx == 64 {
		d0.processBlock(d0.x[:])
		d0.nx = 0
	}

	var k int
	if remain_len+1 <= 448 {
		k = 448 - (int(remain_len) + 1)
	} else {
		k = 960 - (int(remain_len) + 1)
	}
	k++
	if k%8 != 0 {
		panic("Panic in func Sum.padding\n")
	}
	padding := make([]byte, k/8-1)
	d0.Write(padding)

	length_bits := make([]byte, 8)
	binary.BigEndian.PutUint64(length_bits, total_len)
	d0.Write(length_bits)

	if d0.nx != 0 {
		panic("Panic in func Sum.final\n")
	}

	hash := d0.checkSum()
	return append(in, hash[:]...)
}

func (d *digest) checkSum() [32]byte {
	var result [32]byte
	for i := 0; i < 8; i++ {
		binary.BigEndian.PutUint32(result[i*4:], d.h[i])
	}
	return result
}

// Sum computes the final hash and returns it as a byte slice.
func Sum(data []byte) [Size]byte {
	var d digest
	d.Reset()
	padded := pad_message(data)
	for i := 0; i < len(padded); i += BlockSize {
		d.processBlock(padded[i : i+BlockSize])
	}
	return d.checkSum()
}
