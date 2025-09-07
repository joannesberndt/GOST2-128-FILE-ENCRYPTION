// File encryption with GOST2-128 in GCM mode.
// Build:
//   go build -o gost2gcm gost2-128-gcm.go
//
// Usage:
//   ./gost2gcm c <input_file>   -> produces <input_file>.gost2
//   ./gost2gcm d <input_file>   -> removes .gost2 suffix if present, else appends .dec


package main

import (
	"bufio"
	"crypto/rand"
	"encoding/binary"
	"errors"
	"fmt"
	"io"
	"math"
	mrand "math/rand"
	"os"
	"strings"
	"time"
)

// -----------------------------------------------------------------------------
// GOST2-128 + GCM file encrypt/decrypt tool (streaming, block by block)
// -----------------------------------------------------------------------------

// ---------------------- No-echo password input ----------------------
// NOTE: For maximal portability without external modules, we read the password
// via stdin (echo on). 
func getPassword() (string, error) {
	fmt.Print("Enter password: ")
	br := bufio.NewReader(os.Stdin)
	s, err := br.ReadString('\n')
	if err != nil && !errors.Is(err, io.EOF) {
		return "", err
	}
	s = strings.TrimRight(s, "\r\n")
	return s, nil
}

// ---------------------- Portable secure random ----------------------
func secureRandomBytes(n int) ([]byte, error) {
	b := make([]byte, n)
	if _, err := rand.Read(b); err != nil {
		return nil, err
	}
	return b, nil
}

// Last-resort weak RNG (only if all above fail, explicitly requested)
func fallbackWeakRNG(n int) []byte {
	// WARNING: This is NOT cryptographically secure.
	mrand.Seed(time.Now().UnixNano())
	b := make([]byte, n)
	for i := range b {
		b[i] = byte(mrand.Intn(256))
	}
	return b
}

func getIV16() [16]byte {
	var iv [16]byte
	if b, err := secureRandomBytes(16); err == nil {
		copy(iv[:], b)
		return iv
	}
	fmt.Fprintln(os.Stderr, "WARNING: secure RNG unavailable; using weak fallback.")
	copy(iv[:], fallbackWeakRNG(16))
	return iv
}

// ---------------------- GOST2-128 cipher ----------------------

const n1 = 512 // 4096-bit GOST2-128 key for 64 * 64-bit subkeys

var (
	x1, x2 int
	h2     [n1]byte
	h1     [n1 * 3]byte
)

func initHashing() {
	x1, x2 = 0, 0
	for i := 0; i < n1; i++ {
		h2[i] = 0
	}
	for i := 0; i < n1*3; i++ {
		h1[i] = 0
	}
}

func hashing(t1 []byte, b6 int) {
	s4 := [256]byte{
		13, 199, 11, 67, 237, 193, 164, 77, 115, 184, 141, 222, 73, 38, 147, 36, 150, 87, 21, 104, 12, 61, 156, 101, 111, 145,
		119, 22, 207, 35, 198, 37, 171, 167, 80, 30, 219, 28, 213, 121, 86, 29, 214, 242, 6, 4, 89, 162, 110, 175, 19, 157,
		3, 88, 234, 94, 144, 118, 159, 239, 100, 17, 182, 173, 238, 68, 16, 79, 132, 54, 163, 52, 9, 58, 57, 55, 229, 192,
		170, 226, 56, 231, 187, 158, 70, 224, 233, 245, 26, 47, 32, 44, 247, 8, 251, 20, 197, 185, 109, 153, 204, 218, 93, 178,
		212, 137, 84, 174, 24, 120, 130, 149, 72, 180, 181, 208, 255, 189, 152, 18, 143, 176, 60, 249, 27, 227, 128, 139, 243, 253,
		59, 123, 172, 108, 211, 96, 138, 10, 215, 42, 225, 40, 81, 65, 90, 25, 98, 126, 154, 64, 124, 116, 122, 5, 1, 168, 83, 190,
		131, 191, 244, 240, 235, 177, 155, 228, 125, 66, 43, 201, 248, 220, 129, 188, 230, 62, 75, 71, 78, 34, 31, 216, 254, 136, 91,
		114, 106, 46, 217, 196, 92, 151, 209, 133, 51, 236, 33, 252, 127, 179, 69, 7, 183, 105, 146, 97, 39, 15, 205, 112, 200, 166,
		223, 45, 48, 246, 186, 41, 148, 140, 107, 76, 85, 95, 194, 142, 50, 49, 134, 23, 135, 169, 221, 210, 203, 63, 165, 82, 161,
		202, 53, 14, 206, 232, 103, 102, 195, 117, 250, 99, 0, 74, 160, 241, 2, 113,
	}

	b4 := 0
	for b6 > 0 {
		for b6 > 0 && x2 < n1 {
			b5 := t1[b4]
			b4++
			b6--
			h1[x2+n1] = b5
			h1[x2+(n1*2)] = b5 ^ h1[x2]
			x1 = int(h2[x2] ^ s4[b5^byte(x1)])
			h2[x2] = byte(x1)
			x2++
		}
		if x2 == n1 {
			b2 := 0
			x2 = 0
			for b3 := 0; b3 < (n1 + 2); b3++ {
				for b1 := 0; b1 < (n1 * 3); b1++ {
					b2 = int(h1[b1] ^ s4[b2])
					h1[b1] = byte(b2)
				}
				b2 = (b2 + b3) % 256
			}
		}
	}
}

func endHash(h4 *[n1]byte) {
	var h3 [n1]byte
	n4 := n1 - x2
	for i := 0; i < n4; i++ {
		h3[i] = byte(n4)
	}
	hashing(h3[:], n4)
	hashing(h2[:], len(h2))
	for i := 0; i < n1; i++ {
		h4[i] = h1[i]
	}
}

// create 64 * 64-bit subkeys from h4 hash
func createKeys(h4 *[n1]byte) (key [64]uint64) {
	k := 0
	for i := 0; i < 64; i++ {
		var v uint64
		for z := 0; z < 8; z++ {
			v = (v << 8) + uint64(h4[k]&0xff)
			k++
		}
		key[i] = v
	}
	return
}

// S-boxes / tables
var (
	k1  = [16]byte{0x4, 0xA, 0x9, 0x2, 0xD, 0x8, 0x0, 0xE, 0x6, 0xB, 0x1, 0xC, 0x7, 0xF, 0x5, 0x3}
	k2  = [16]byte{0xE, 0xB, 0x4, 0xC, 0x6, 0xD, 0xF, 0xA, 0x2, 0x3, 0x8, 0x1, 0x0, 0x7, 0x5, 0x9}
	k3  = [16]byte{0x5, 0x8, 0x1, 0xD, 0xA, 0x3, 0x4, 0x2, 0xE, 0xF, 0xC, 0x7, 0x6, 0x0, 0x9, 0xB}
	k4  = [16]byte{0x7, 0xD, 0xA, 0x1, 0x0, 0x8, 0x9, 0xF, 0xE, 0x4, 0x6, 0xC, 0xB, 0x2, 0x5, 0x3}
	k5  = [16]byte{0x6, 0xC, 0x7, 0x1, 0x5, 0xF, 0xD, 0x8, 0x4, 0xA, 0x9, 0xE, 0x0, 0x3, 0xB, 0x2}
	k6  = [16]byte{0x4, 0xB, 0xA, 0x0, 0x7, 0x2, 0x1, 0xD, 0x3, 0x6, 0x8, 0x5, 0x9, 0xC, 0xF, 0xE}
	k7  = [16]byte{0xD, 0xB, 0x4, 0x1, 0x3, 0xF, 0x5, 0x9, 0x0, 0xA, 0xE, 0x7, 0x6, 0x8, 0x2, 0xC}
	k8  = [16]byte{0x1, 0xF, 0xD, 0x0, 0x5, 0x7, 0xA, 0x4, 0x9, 0x2, 0x3, 0xE, 0x6, 0xB, 0x8, 0xC}
	k9  = [16]byte{0xC, 0x4, 0x6, 0x2, 0xA, 0x5, 0xB, 0x9, 0xE, 0x8, 0xD, 0x7, 0x0, 0x3, 0xF, 0x1}
	k10 = [16]byte{0x6, 0x8, 0x2, 0x3, 0x9, 0xA, 0x5, 0xC, 0x1, 0xE, 0x4, 0x7, 0xB, 0xD, 0x0, 0xF}
	k11 = [16]byte{0xB, 0x3, 0x5, 0x8, 0x2, 0xF, 0xA, 0xD, 0xE, 0x1, 0x7, 0x4, 0xC, 0x9, 0x6, 0x0}
	k12 = [16]byte{0xC, 0x8, 0x2, 0x1, 0xD, 0x4, 0xF, 0x6, 0x7, 0x0, 0xA, 0x5, 0x3, 0xE, 0x9, 0xB}
	k13 = [16]byte{0x7, 0xF, 0x5, 0xA, 0x8, 0x1, 0x6, 0xD, 0x0, 0x9, 0x3, 0xE, 0xB, 0x4, 0x2, 0xC}
	k14 = [16]byte{0x5, 0xD, 0xF, 0x6, 0x9, 0x2, 0xC, 0xA, 0xB, 0x7, 0x8, 0x1, 0x4, 0x3, 0xE, 0x0}
	k15 = [16]byte{0x8, 0xE, 0x2, 0x5, 0x6, 0x9, 0x1, 0xC, 0xF, 0x4, 0xB, 0x0, 0xD, 0xA, 0x3, 0x7}
	k16 = [16]byte{0x1, 0x7, 0xE, 0xD, 0x0, 0x5, 0x8, 0x3, 0x4, 0xF, 0xA, 0x6, 0x9, 0xC, 0xB, 0x2}
)

var (
	k175 [256]byte
	k153 [256]byte
	k131 [256]byte
	k109 [256]byte
	k87  [256]byte
	k65  [256]byte
	k43  [256]byte
	k21  [256]byte
)

func kboxinit() {
	for i := 0; i < 256; i++ {
		k175[i] = (k16[byte(i)>>4] << 4) | k15[byte(i)&15]
		k153[i] = (k14[byte(i)>>4] << 4) | k13[byte(i)&15]
		k131[i] = (k12[byte(i)>>4] << 4) | k11[byte(i)&15]
		k109[i] = (k10[byte(i)>>4] << 4) | k9[byte(i)&15]
		k87[i] = (k8[byte(i)>>4] << 4) | k7[byte(i)&15]
		k65[i] = (k6[byte(i)>>4] << 4) | k5[byte(i)&15]
		k43[i] = (k4[byte(i)>>4] << 4) | k3[byte(i)&15]
		k21[i] = (k2[byte(i)>>4] << 4) | k1[byte(i)&15]
	}
}

func fGOST(x uint64) uint64 {
	y := x >> 32
	z := x & 0xffffffff
	y = (uint64(k87[(y>>24)&255]) << 24) | (uint64(k65[(y>>16)&255]) << 16) |
		(uint64(k43[(y>>8)&255]) << 8) | uint64(k21[y&255])
	z = (uint64(k175[(z>>24)&255]) << 24) | (uint64(k153[(z>>16)&255]) << 16) |
		(uint64(k131[(z>>8)&255]) << 8) | uint64(k109[z&255])
	x = (y << 32) | (z & 0xffffffff)
	return (x<<11 | x>>(64-11))
}

func gostcrypt(in [2]uint64, key *[64]uint64) (out [2]uint64) {
	a := in[0]
	b := in[1]
	k := 0
	for r := 0; r < 32; r++ {
		b ^= fGOST(a + key[k])
		k++
		a ^= fGOST(b + key[k])
		k++
	}
	out[0] = b
	out[1] = a
	return
}

func gostdecrypt(in [2]uint64, key *[64]uint64) (out [2]uint64) {
	a := in[0]
	b := in[1]
	k := 63
	for r := 0; r < 32; r++ {
		b ^= fGOST(a + key[k])
		k--
		a ^= fGOST(b + key[k])
		k--
	}
	out[0] = b
	out[1] = a
	return
}

// ---------------------- GCM helpers (128-bit ops) ----------------------

type be128 struct{ hi, lo uint64 } // big-endian logical 128-bit

func loadBE128(b []byte) be128 {
	_ = b[15]
	return be128{
		hi: uint64(b[0])<<56 | uint64(b[1])<<48 | uint64(b[2])<<40 | uint64(b[3])<<32 |
			uint64(b[4])<<24 | uint64(b[5])<<16 | uint64(b[6])<<8 | uint64(b[7]),
		lo: uint64(b[8])<<56 | uint64(b[9])<<48 | uint64(b[10])<<40 | uint64(b[11])<<32 |
			uint64(b[12])<<24 | uint64(b[13])<<16 | uint64(b[14])<<8 | uint64(b[15]),
	}
}

func storeBE128(x be128, b []byte) {
	_ = b[15]
	b[0] = byte(x.hi >> 56)
	b[1] = byte(x.hi >> 48)
	b[2] = byte(x.hi >> 40)
	b[3] = byte(x.hi >> 32)
	b[4] = byte(x.hi >> 24)
	b[5] = byte(x.hi >> 16)
	b[6] = byte(x.hi >> 8)
	b[7] = byte(x.hi)
	b[8] = byte(x.lo >> 56)
	b[9] = byte(x.lo >> 48)
	b[10] = byte(x.lo >> 40)
	b[11] = byte(x.lo >> 32)
	b[12] = byte(x.lo >> 24)
	b[13] = byte(x.lo >> 16)
	b[14] = byte(x.lo >> 8)
	b[15] = byte(x.lo)
}

func be128Xor(a, b be128) be128 { return be128{a.hi ^ b.hi, a.lo ^ b.lo} }

// right shift by 1 bit (big-endian logical value)
func be128Shr1(v be128) be128 {
	return be128{hi: v.hi >> 1, lo: (v.lo >> 1) | ((v.hi & 1) << 63)}
}

// left shift by 1 bit
func be128Shl1(v be128) be128 {
	return be128{hi: (v.hi << 1) | (v.lo >> 63), lo: (v.lo << 1)}
}

// GF(2^128) multiplication per SP 800-38D, right-shift method
func gfMult(X, Y be128) be128 {
	Z := be128{0, 0}
	V := Y
	R := be128{0xE100000000000000, 0x0000000000000000} // R constant (big-endian)

	for i := 0; i < 128; i++ {
		msb := (X.hi & 0x8000000000000000) != 0
		if msb {
			Z = be128Xor(Z, V)
		}
		lsb := (V.lo & 1) != 0
		V = be128Shr1(V)
		if lsb {
			V = be128Xor(V, R)
		}
		X = be128Shl1(X)
	}
	return Z
}

// GHASH update: Y <- (Y ^ X) * H
func ghashUpdate(Y *be128, H be128, block []byte) {
	X := loadBE128(block)
	*Y = gfMult(be128Xor(*Y, X), H)
}

// Encrypt a single 16-byte block with GOST2-128
func gostEncryptBlock(in []byte, out []byte, key *[64]uint64) {
	var inw [2]uint64
	inw[0] = binary.BigEndian.Uint64(in[0:8])
	inw[1] = binary.BigEndian.Uint64(in[8:16])
	outw := gostcrypt(inw, key)
	binary.BigEndian.PutUint64(out[0:8], outw[0])
	binary.BigEndian.PutUint64(out[8:16], outw[1])
}

// Compute H = E_K(0^128)
func computeH(H []byte, key *[64]uint64) {
	var zero [16]byte
	gostEncryptBlock(zero[:], H, key)
}

// inc32 on the last 32 bits of a 128-bit counter (big-endian)
func inc32(ctr []byte) {
	c := binary.BigEndian.Uint32(ctr[12:16])
	c = c + 1
	binary.BigEndian.PutUint32(ctr[12:16], c)
}

// Derive J0 from IV (generic case when IV != 12 bytes). Here IV is 16 bytes.
func deriveJ0(J0 []byte, iv []byte, Hbe be128) {
	// Y = 0
	Y := be128{0, 0}
	block := make([]byte, 16)

	// Process full 16-byte blocks of IV
	off := 0
	for len(iv)-off >= 16 {
		ghashUpdate(&Y, Hbe, iv[off:off+16])
		off += 16
	}
	// Last partial block (pad with zeros)
	if len(iv)-off > 0 {
		for i := range block {
			block[i] = 0
		}
		copy(block, iv[off:])
		ghashUpdate(&Y, Hbe, block)
	}
	// Append 128-bit length block: 64-bit zeros || [len(IV) in bits]_64
	for i := range block {
		block[i] = 0
	}
	ivbits := uint64(len(iv)) * 8
	binary.BigEndian.PutUint64(block[8:], ivbits)
	ghashUpdate(&Y, Hbe, block)

	storeBE128(Y, J0)
}

// Prepares GHASH lengths block for AAD(empty) and C(lenC)
func ghashLengthsUpdate(Y *be128, Hbe be128, aadBits, cBits uint64) {
	lenblk := make([]byte, 16)
	// [len(AAD)]_64 || [len(C)]_64 in bits, both big-endian; AAD=0
	binary.BigEndian.PutUint64(lenblk[0:8], aadBits)
	binary.BigEndian.PutUint64(lenblk[8:16], cBits)
	ghashUpdate(Y, Hbe, lenblk)
}

// Constant-time tag comparison
func ctMemcmp(a, b []byte) int {
	if len(a) != len(b) {
		return 1
	}
	var r byte
	for i := 0; i < len(a); i++ {
		r |= a[i] ^ b[i]
	}
	if r == 0 {
		return 0
	}
	return 1
}

// ---------------------- File name helpers ----------------------
func addSuffixGOST2(in string) string  { return in + ".gost2" }
func stripSuffixGOST2(in string) string {
	if strings.HasSuffix(in, ".gost2") {
		return in[:len(in)-len(".gost2")]
	}
	return in + ".dec"
}

// ---------------------- High-level encrypt/decrypt ----------------------

const bufChunk = 4096

func encryptFile(infile, outfile string, key *[64]uint64) error {
	fi, err := os.Open(infile)
	if err != nil {
		return fmt.Errorf("open input: %w", err)
	}
	defer fi.Close()

	fo, err := os.Create(outfile)
	if err != nil {
		return fmt.Errorf("open output: %w", err)
	}
	defer func() {
		_ = fo.Sync()
		fo.Close()
	}()

	// Compute H and J0
	H := make([]byte, 16)
	computeH(H, key)
	Hbe := loadBE128(H)

	iv := getIV16()

	// Write IV (16 bytes)
	if _, err := fo.Write(iv[:]); err != nil {
		return fmt.Errorf("write IV: %w", err)
	}

	J0 := make([]byte, 16)
	deriveJ0(J0, iv[:], Hbe)

	// S = GHASH over ciphertext (starts at 0)
	S := be128{0, 0}

	// Counter starts from inc32(J0)
	ctr := make([]byte, 16)
	copy(ctr, J0)
	inc32(ctr)

	// Streaming encrypt
	inbuf := make([]byte, bufChunk)
	totalCBytes := uint64(0)

	for {
		rn, rerr := fi.Read(inbuf)
		if rn == 0 && rerr != nil {
			if errors.Is(rerr, io.EOF) {
				break
			}
			return fmt.Errorf("read input: %w", rerr)
		}
		off := 0
		for off < rn {
			n := int(math.Min(16, float64(rn-off)))
			ks := make([]byte, 16)
			cblk := make([]byte, 16)
			pblk := make([]byte, 16)

			// keystream = E_K(ctr)
			gostEncryptBlock(ctr, ks, key)
			inc32(ctr)

			copy(pblk, inbuf[off:off+n])
			for i := 0; i < n; i++ {
				cblk[i] = pblk[i] ^ ks[i]
			}
			// pad remaining of cblk with zeros for GHASH
			ghashUpdate(&S, Hbe, cblk)

			// Write only n bytes
			if _, err := fo.Write(cblk[:n]); err != nil {
				return fmt.Errorf("write C: %w", err)
			}
			totalCBytes += uint64(n)
			off += n
		}
	}

	// S <- S ⊗ H with lengths block (AAD=0, C=totalCBytes)
	ghashLengthsUpdate(&S, Hbe, 0, totalCBytes*8)

	// Tag T = E_K(J0) XOR S
	EJ0 := make([]byte, 16)
	gostEncryptBlock(J0, EJ0, key)
	Sbytes := make([]byte, 16)
	storeBE128(S, Sbytes)
	Tag := make([]byte, 16)
	for i := 0; i < 16; i++ {
		Tag[i] = EJ0[i] ^ Sbytes[i]
	}

	// Write TAG
	if _, err := fo.Write(Tag); err != nil {
		return fmt.Errorf("write TAG: %w", err)
	}

	fmt.Println("Encryption completed. Wrote IV + ciphertext + tag.")
	return nil
}

func fileSize(path string) (int64, error) {
	fi, err := os.Stat(path)
	if err != nil {
		return 0, err
	}
	return fi.Size(), nil
}

func decryptFile(infile, outfile string, key *[64]uint64) (int, error) {
	fi, err := os.Open(infile)
	if err != nil {
		return 1, fmt.Errorf("open input: %w", err)
	}
	defer fi.Close()

	sz, err := fileSize(infile)
	if err != nil {
		return 1, fmt.Errorf("stat: %w", err)
	}
	if sz < 32 {
		return 1, fmt.Errorf("file too small (needs at least IV+TAG)")
	}

	iv := make([]byte, 16)
	if _, err := io.ReadFull(fi, iv); err != nil {
		return 1, fmt.Errorf("read IV: %w", err)
	}
	remaining := sz - 16
	if remaining < 16 {
		return 1, fmt.Errorf("missing tag")
	}
	ciphLen := remaining - 16

	fo, err := os.Create(outfile)
	if err != nil {
		return 1, fmt.Errorf("open output: %w", err)
	}
	defer func() {
		_ = fo.Sync()
		fo.Close()
	}()

	// Compute H and J0 as in encryption
	H := make([]byte, 16)
	computeH(H, key)
	Hbe := loadBE128(H)
	J0 := make([]byte, 16)
	deriveJ0(J0, iv, Hbe)

	// GHASH S over ciphertext
	S := be128{0, 0}

	// CTR starts at inc32(J0)
	ctr := make([]byte, 16)
	copy(ctr, J0)
	inc32(ctr)

	left := ciphLen
	buf := make([]byte, bufChunk)
	for left > 0 {
		toRead := int64(bufChunk)
		if left < toRead {
			toRead = left
		}
		rn, err := io.ReadFull(fi, buf[:toRead])
		if err != nil {
			if errors.Is(err, io.ErrUnexpectedEOF) && int64(rn) == toRead {
				// ok
			} else if errors.Is(err, io.EOF) && rn > 0 {
				// ok
			} else if errors.Is(err, io.ErrUnexpectedEOF) && rn > 0 {
				// ok
			} else if errors.Is(err, io.EOF) && rn == 0 {
				break
			} else {
				return 1, fmt.Errorf("read C: %w", err)
			}
		}

		off := 0
		for off < rn {
			n := int(math.Min(16, float64(rn-off)))
			ks := make([]byte, 16)
			cblk := make([]byte, 16)
			pblk := make([]byte, 16)
			copy(cblk, buf[off:off+n]) // zero-padded for GHASH

			ghashUpdate(&S, Hbe, cblk)

			gostEncryptBlock(ctr, ks, key)
			inc32(ctr)

			for i := 0; i < n; i++ {
				pblk[i] = cblk[i] ^ ks[i]
			}
			if _, err := fo.Write(pblk[:n]); err != nil {
				return 1, fmt.Errorf("write P: %w", err)
			}
			off += n
		}
		left -= int64(rn)
	}

	// Read trailing TAG
	Tag := make([]byte, 16)
	if _, err := io.ReadFull(fi, Tag); err != nil {
		return 1, fmt.Errorf("read TAG: %w", err)
	}

	// Finalize GHASH with lengths
	cBits := uint64(ciphLen) * 8
	ghashLengthsUpdate(&S, Hbe, 0, cBits)

	// Compute expected tag: E_K(J0) XOR S
	EJ0 := make([]byte, 16)
	Stmp := make([]byte, 16)
	Tcalc := make([]byte, 16)

	gostEncryptBlock(J0, EJ0, key)
	storeBE128(S, Stmp)
	for i := 0; i < 16; i++ {
		Tcalc[i] = EJ0[i] ^ Stmp[i]
	}

	diff := ctMemcmp(Tag, Tcalc)
	if diff == 0 {
		fmt.Println("Authentication: OK")
		return 0, nil
	}
	fmt.Println("Authentication: FAILED")
	return 1, nil
}

// ---------------------- Derive GOST2-128 subkeys from password ----------------------
func deriveKeyFromPassword(pwd string) (key [64]uint64) {
	var h4 [n1]byte
	initHashing()
	hashing([]byte(pwd), len(pwd))
	endHash(&h4)
	key = createKeys(&h4)
	// best effort: zeroize h4
	for i := range h4 {
		h4[i] = 0
	}
	return
}

// ---------------------- Main ----------------------
func usage(prog string) {
	fmt.Fprintf(os.Stderr, "Usage: %s c|d <input_file>\n", prog)
}

func main() {
	if len(os.Args) != 3 {
		usage(os.Args[0])
		os.Exit(2)
	}
	mode := os.Args[1]
	infile := os.Args[2]

	pwd, err := getPassword()
	if err != nil {
		fmt.Fprintln(os.Stderr, "Failed to read password:", err)
		os.Exit(2)
	}

	// Init GOST2 tables and derive subkeys from password
	kboxinit()
	key := deriveKeyFromPassword(pwd)

	// Best-effort wipe of password string (Go strings are immutable; we can only shadow)
	pwd = ""
	_ = pwd

	var outfile string
	switch strings.ToLower(mode) {
	case "c":
		outfile = addSuffixGOST2(infile)
		if err := encryptFile(infile, outfile, &key); err != nil {
			fmt.Fprintln(os.Stderr, "encrypt:", err)
			os.Exit(1)
		}
	case "d":
		outfile = stripSuffixGOST2(infile)
		rc, err := decryptFile(infile, outfile, &key)
		if err != nil {
			fmt.Fprintln(os.Stderr, "decrypt:", err)
			os.Exit(1)
		}
		if rc != 0 {
			os.Exit(1)
		}
	default:
		usage(os.Args[0])
		os.Exit(2)
	}
}
