// GOST2-128 File Encryptor/Decryptor (CBC + SHA-256 authentication)
//
// Build:
//   go build -o gost2file gost2-128-cbc.go
//
// Usage:
//   ./gost2file c <input_file>   -> produces <input_file>.gost2
//   ./gost2file d <input_file>   -> removes .gost2 suffix if present, else appends .dec
//
// File format (encrypted):
//   [16 bytes IV (clear)] [ciphertext (PKCS#7 padded)] [32 bytes SHA-256 over ciphertext only]
//
// Password:
//   Asked interactively. On Unix (Linux/macOS/BSD) no-echo; on other OS (including Windows here) falls back to echoing.
//   For Windows, we use a safe echo fallback.
//
// Randomness:
//   - Preferred: crypto/rand.Read
//   - Else (LAST RESORT): simple PRNG from time.Now()
//
//
// =========================
//           Package
// =========================
package main

import (
	"bufio"
	"crypto/rand"
	"crypto/sha256"
	"encoding/binary"
	"errors"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"runtime"
	"strings"
	"syscall"
	"time"
	"unsafe"
)

// =========================
//    GOST2-128 CORE PARTS
// =========================
const n1 = 512 // 4096-bit key -> 64 * 64-bit subkeys

type word64 = uint64

var (
	x1, x2 int
	h2     [n1]byte
	h1     [n1 * 3]byte
)

// init sets everything to zero
func initState() {
	x1, x2 = 0, 0
	for i := 0; i < n1; i++ {
		h2[i] = 0
		h1[i] = 0
	}
}

func hashing(t1 []byte, b6 int) {
	s4 := [256]byte{
		13, 199, 11, 67, 237, 193, 164, 77, 115, 184, 141, 222, 73,
		38, 147, 36, 150, 87, 21, 104, 12, 61, 156, 101, 111, 145,
		119, 22, 207, 35, 198, 37, 171, 167, 80, 30, 219, 28, 213,
		121, 86, 29, 214, 242, 6, 4, 89, 162, 110, 175, 19, 157,
		3, 88, 234, 94, 144, 118, 159, 239, 100, 17, 182, 173, 238,
		68, 16, 79, 132, 54, 163, 52, 9, 58, 57, 55, 229, 192,
		170, 226, 56, 231, 187, 158, 70, 224, 233, 245, 26, 47, 32,
		44, 247, 8, 251, 20, 197, 185, 109, 153, 204, 218, 93, 178,
		212, 137, 84, 174, 24, 120, 130, 149, 72, 180, 181, 208, 255,
		189, 152, 18, 143, 176, 60, 249, 27, 227, 128, 139, 243, 253,
		59, 123, 172, 108, 211, 96, 138, 10, 215, 42, 225, 40, 81,
		65, 90, 25, 98, 126, 154, 64, 124, 116, 122, 5, 1, 168,
		83, 190, 131, 191, 244, 240, 235, 177, 155, 228, 125, 66, 43,
		201, 248, 220, 129, 188, 230, 62, 75, 71, 78, 34, 31, 216,
		254, 136, 91, 114, 106, 46, 217, 196, 92, 151, 209, 133, 51,
		236, 33, 252, 127, 179, 69, 7, 183, 105, 146, 97, 39, 15,
		205, 112, 200, 166, 223, 45, 48, 246, 186, 41, 148, 140, 107,
		76, 85, 95, 194, 142, 50, 49, 134, 23, 135, 169, 221, 210,
		203, 63, 165, 82, 161, 202, 53, 14, 206, 232, 103, 102, 195,
		117, 250, 99, 0, 74, 160, 241, 2, 113,
	}
	b4 := 0
	for b6 > 0 {
		for b6 > 0 && x2 < n1 {
			b5 := t1[b4]
			b4++
			h1[x2+n1] = b5
			h1[x2+(n1*2)] = b5 ^ h1[x2]
			x1 = int(h2[x2] ^ s4[byte(b5^byte(x1))])
			h2[x2] = byte(x1)
			x2++
			b6--
		}
		if x2 == n1 {
			b2 := 0
			x2 = 0
			for b3 := 0; b3 < n1+2; b3++ {
				for b1 := 0; b1 < n1*3; b1++ {
					b2 = int(h1[b1] ^ s4[byte(b2)])
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

func createKeys(h4 *[n1]byte, key *[64]word64) {
	k := 0
	for i := 0; i < 64; i++ {
		key[i] = 0
		for z := 0; z < 8; z++ {
			key[i] = (key[i] << 8) + word64(h4[k]&0xff)
			k++
		}
	}
}

// Substitution tables
var (
	k1 = [16]byte{0x4, 0xA, 0x9, 0x2, 0xD, 0x8, 0x0, 0xE, 0x6, 0xB, 0x1, 0xC, 0x7, 0xF, 0x5, 0x3}
	k2 = [16]byte{0xE, 0xB, 0x4, 0xC, 0x6, 0xD, 0xF, 0xA, 0x2, 0x3, 0x8, 0x1, 0x0, 0x7, 0x5, 0x9}
	k3 = [16]byte{0x5, 0x8, 0x1, 0xD, 0xA, 0x3, 0x4, 0x2, 0xE, 0xF, 0xC, 0x7, 0x6, 0x0, 0x9, 0xB}
	k4 = [16]byte{0x7, 0xD, 0xA, 0x1, 0x0, 0x8, 0x9, 0xF, 0xE, 0x4, 0x6, 0xC, 0xB, 0x2, 0x5, 0x3}
	k5 = [16]byte{0x6, 0xC, 0x7, 0x1, 0x5, 0xF, 0xD, 0x8, 0x4, 0xA, 0x9, 0xE, 0x0, 0x3, 0xB, 0x2}
	k6 = [16]byte{0x4, 0xB, 0xA, 0x0, 0x7, 0x2, 0x1, 0xD, 0x3, 0x6, 0x8, 0x5, 0x9, 0xC, 0xF, 0xE}
	k7 = [16]byte{0xD, 0xB, 0x4, 0x1, 0x3, 0xF, 0x5, 0x9, 0x0, 0xA, 0xE, 0x7, 0x6, 0x8, 0x2, 0xC}
	k8 = [16]byte{0x1, 0xF, 0xD, 0x0, 0x5, 0x7, 0xA, 0x4, 0x9, 0x2, 0x3, 0xE, 0x6, 0xB, 0x8, 0xC}
	k9 = [16]byte{0xC, 0x4, 0x6, 0x2, 0xA, 0x5, 0xB, 0x9, 0xE, 0x8, 0xD, 0x7, 0x0, 0x3, 0xF, 0x1}
	k10 = [16]byte{0x6, 0x8, 0x2, 0x3, 0x9, 0xA, 0x5, 0xC, 0x1, 0xE, 0x4, 0x7, 0xB, 0xD, 0x0, 0xF}
	k11 = [16]byte{0xB, 0x3, 0x5, 0x8, 0x2, 0xF, 0xA, 0xD, 0xE, 0x1, 0x7, 0x4, 0xC, 0x9, 0x6, 0x0}
	k12 = [16]byte{0xC, 0x8, 0x2, 0x1, 0xD, 0x4, 0xF, 0x6, 0x7, 0x0, 0xA, 0x5, 0x3, 0xE, 0x9, 0xB}
	k13 = [16]byte{0x7, 0xF, 0x5, 0xA, 0x8, 0x1, 0x6, 0xD, 0x0, 0x9, 0x3, 0xE, 0xB, 0x4, 0x2, 0xC}
	k14 = [16]byte{0x5, 0xD, 0xF, 0x6, 0x9, 0x2, 0xC, 0xA, 0xB, 0x7, 0x8, 0x1, 0x4, 0x3, 0xE, 0x0}
	k15 = [16]byte{0x8, 0xE, 0x2, 0x5, 0x6, 0x9, 0x1, 0xC, 0xF, 0x4, 0xB, 0x0, 0xD, 0xA, 0x3, 0x7}
	k16 = [16]byte{0x1, 0x7, 0xE, 0xD, 0x0, 0x5, 0x8, 0x3, 0x4, 0xF, 0xA, 0x6, 0x9, 0xC, 0xB, 0x2}

	k175, k153, k131, k109, k87, k65, k43, k21 [256]byte
)

func kboxinit() {
	for i := 0; i < 256; i++ {
		k175[i] = k16[i>>4]<<4 | k15[i&15]
		k153[i] = k14[i>>4]<<4 | k13[i&15]
		k131[i] = k12[i>>4]<<4 | k11[i&15]
		k109[i] = k10[i>>4]<<4 | k9[i&15]
		k87[i] = k8[i>>4]<<4 | k7[i&15]
		k65[i] = k6[i>>4]<<4 | k5[i&15]
		k43[i] = k4[i>>4]<<4 | k3[i&15]
		k21[i] = k2[i>>4]<<4 | k1[i&15]
	}
}

func f(x word64) word64 {
	y := x >> 32
	z := x & 0xffffffff
	y = word64(k87[(y>>24)&255])<<24 | word64(k65[(y>>16)&255])<<16 |
		word64(k43[(y>>8)&255])<<8 | word64(k21[y&255])
	z = word64(k175[(z>>24)&255])<<24 | word64(k153[(z>>16)&255])<<16 |
		word64(k131[(z>>8)&255])<<8 | word64(k109[z&255])
	x = (y << 32) | (z & 0xffffffff)
	return (x << 11) | (x >> (64 - 11))
}

func gostcrypt(in [2]word64, key [64]word64) (out [2]word64) {
	ng1, ng2 := in[0], in[1]
	k := 0
	for i := 0; i < 32; i++ {
		ng2 ^= f(ng1 + key[k])
		k++
		ng1 ^= f(ng2 + key[k])
		k++
	}
	out[0] = ng2
	out[1] = ng1
	return
}

func gostdecrypt(in [2]word64, key [64]word64) (out [2]word64) {
	ng1, ng2 := in[0], in[1]
	k := 63
	for i := 0; i < 32; i++ {
		ng2 ^= f(ng1 + key[k])
		k--
		ng1 ^= f(ng2 + key[k])
		k--
	}
	out[0] = ng2
	out[1] = ng1
	return
}



// =========================
//          Utilities
// =========================

const (
	BLOCK_SIZE = 16
	READ_CHUNK = 64 * 1024
)

// Big-endian bytes<->words helpers (128-bit block -> two 64-bit words)
func beBytesToWords(in []byte) (out [2]word64) {
	out[0] = word64(binary.BigEndian.Uint64(in[0:8]))
	out[1] = word64(binary.BigEndian.Uint64(in[8:16]))
	return
}

func beWordsToBytes(in [2]word64, out []byte) {
	binary.BigEndian.PutUint64(out[0:8], uint64(in[0]))
	binary.BigEndian.PutUint64(out[8:16], uint64(in[1]))
}

// Cross-platform-ish password prompt with best-effort no-echo on Unix.
// On non-Unix (including Windows in this single-file version), we fall back to echo input.
func promptPassword(prompt string) (string, error) {
	fmt.Fprint(os.Stdout, prompt)
	// Unix-like branch: try disabling echo with termios via ioctl
	if runtime.GOOS == "linux" || runtime.GOOS == "darwin" || runtime.GOOS == "freebsd" || runtime.GOOS == "openbsd" || runtime.GOOS == "netbsd" {
		fd := int(os.Stdin.Fd())

		type termios struct {
			Iflag  uint32
			Oflag  uint32
			Cflag  uint32
			Lflag  uint32
			Cc     [20]byte
			Ispeed uint32
			Ospeed uint32
		}

		var oldState termios
		_, _, errno := syscall.Syscall6(syscall.SYS_IOCTL, uintptr(fd),
			uintptr(syscall.TCGETS), uintptr(unsafe.Pointer(&oldState)), 0, 0, 0)
		if errno == 0 {
			newState := oldState
			newState.Lflag &^= syscall.ECHO
			_, _, errno = syscall.Syscall6(syscall.SYS_IOCTL, uintptr(fd),
				uintptr(syscall.TCSETS), uintptr(unsafe.Pointer(&newState)), 0, 0, 0)
		}
		reader := bufio.NewReader(os.Stdin)
		line, err := reader.ReadString('\n')
		// Restore state
		if errno == 0 {
			_, _, _ = syscall.Syscall6(syscall.SYS_IOCTL, uintptr(fd),
				uintptr(syscall.TCSETS), uintptr(unsafe.Pointer(&oldState)), 0, 0, 0)
		}
		fmt.Fprintln(os.Stdout)
		if err != nil && !errors.Is(err, io.EOF) {
			return "", err
		}
		return strings.TrimRight(line, "\r\n"), nil
	}

	// Fallback (e.g., Windows): read with echo
	fmt.Fprintln(os.Stderr, "Warning: password will be echoed (no-echo unsupported on this OS in single-file mode).")
	reader := bufio.NewReader(os.Stdin)
	line, err := reader.ReadString('\n')
	fmt.Fprintln(os.Stdout)
	if err != nil && !errors.Is(err, io.EOF) {
		return "", err
	}
	return strings.TrimRight(line, "\r\n"), nil
}

// IV generation (preferred crypto/rand, else LAST RESORT pseudo-random)
func generateIV() [BLOCK_SIZE]byte {
	var iv [BLOCK_SIZE]byte
	if _, err := rand.Read(iv[:]); err == nil {
		return iv
	}
	// LAST RESORT (not recommended): time-based PRNG
	var x uint64 = uint64(time.Now().UnixNano()*6364136223846793005 + 1)
	for i := 0; i < BLOCK_SIZE; i++ {
		x ^= x << 13
		x ^= x >> 7
		x ^= x << 17
		iv[i] = byte(x & 0xFF)
	}
	return iv
}

// Derive 4096-bit key material from password using MD2II-based hashing
func deriveGOSTSubkeysFromPassword(password string) (subkeys [64]word64) {
	var h4 [n1]byte
	initState()
	pass := []byte(password)
	hashing(pass, len(pass))
	endHash(&h4)
	createKeys(&h4, &subkeys)
	for i := range pass { // best-effort clear
		pass[i] = 0
	}
	return
}

// PKCS#7 padding
func pkcs7Pad(buf []byte, used int) ([]byte, error) {
	pad := BLOCK_SIZE - (used % BLOCK_SIZE)
	out := make([]byte, used+pad)
	copy(out, buf[:used])
	for i := 0; i < pad; i++ {
		out[used+i] = byte(pad)
	}
	return out, nil
}

func pkcs7Unpad(buf []byte) ([]byte, error) {
	if len(buf) == 0 || len(buf)%BLOCK_SIZE != 0 {
		return nil, fmt.Errorf("invalid length for PKCS#7")
	}
	pad := int(buf[len(buf)-1])
	if pad == 0 || pad > BLOCK_SIZE {
		return nil, fmt.Errorf("invalid padding size")
	}
	for i := 0; i < pad; i++ {
		if buf[len(buf)-1-i] != byte(pad) {
			return nil, fmt.Errorf("invalid padding bytes")
		}
	}
	return buf[:len(buf)-pad], nil
}

// Output filename helpers
func hasSuffix(name, suffix string) bool {
	return strings.HasSuffix(name, suffix)
}

func makeOutputNameEncrypt(in string) string {
	return in + ".gost2"
}

func makeOutputNameDecrypt(in string) string {
	if hasSuffix(in, ".gost2") {
		return strings.TrimSuffix(in, ".gost2")
	}
	return in + ".dec"
}

// =========================
//   CBC Encrypt / Decrypt
// =========================

// cbcEncryptStream writes [IV][CIPHERTEXT][SHA256(CIPHERTEXT)] to fout.
func cbcEncryptStream(fin *os.File, fout *os.File, subkeys [64]word64) error {
	// Write IV first (clear)
	iv := generateIV()
	if _, err := fout.Write(iv[:]); err != nil {
		return err
	}

	prev := iv
	hasher := sha256.New()

	inbuf := make([]byte, READ_CHUNK+BLOCK_SIZE) // extra for padding
	outbuf := make([]byte, READ_CHUNK+BLOCK_SIZE)

	reader := bufio.NewReader(fin)

	var carry []byte // remainder < 16 from previous read

	for {
		n, err := reader.Read(inbuf)
		if n > 0 {
			// prepend carry if any
			var chunk []byte
			if len(carry) > 0 {
				chunk = append(append([]byte{}, carry...), inbuf[:n]...)
			} else {
				chunk = inbuf[:n]
			}

			// Process all full blocks, keep remainder as carry
			full := (len(chunk) / BLOCK_SIZE) * BLOCK_SIZE
			rem := len(chunk) - full

			// encrypt full blocks in place
			for off := 0; off < full; off += BLOCK_SIZE {
				// XOR with prev (CBC)
				for i := 0; i < BLOCK_SIZE; i++ {
					chunk[off+i] ^= prev[i]
				}
				inw := beBytesToWords(chunk[off : off+BLOCK_SIZE])
				outw := gostcrypt(inw, subkeys)
				beWordsToBytes(outw, outbuf[off:off+BLOCK_SIZE])
				copy(prev[:], outbuf[off:off+BLOCK_SIZE])
			}

			// write ciphertext of full blocks
			if full > 0 {
				if _, werr := fout.Write(outbuf[:full]); werr != nil {
					return werr
				}
				if _, herr := hasher.Write(outbuf[:full]); herr != nil {
					return herr
				}
			}

			// save remainder as carry
			if rem > 0 {
				carry = append(carry[:0], chunk[full:]...)
			} else {
				carry = carry[:0]
			}
		}

		if err == io.EOF {
			break
		}
		if err != nil {
			return err
		}
	}

	// Final: pad the carry and encrypt
	padded, err := pkcs7Pad(carry, len(carry))
	if err != nil {
		return err
	}
	total := len(padded)
	for off := 0; off < total; off += BLOCK_SIZE {
		// CBC XOR
		for i := 0; i < BLOCK_SIZE; i++ {
			padded[off+i] ^= prev[i]
		}
		inw := beBytesToWords(padded[off : off+BLOCK_SIZE])
		outw := gostcrypt(inw, subkeys)
		beWordsToBytes(outw, outbuf[off:off+BLOCK_SIZE])
		copy(prev[:], outbuf[off:off+BLOCK_SIZE])
	}
	if _, werr := fout.Write(outbuf[:total]); werr != nil {
		return werr
	}
	if _, herr := hasher.Write(outbuf[:total]); herr != nil {
		return herr
	}

	// write SHA-256 over ciphertext only (not including IV)
	sum := hasher.Sum(nil)
	if _, err := fout.Write(sum); err != nil {
		return err
	}
	return nil
}

// cbcDecryptStream reads [IV][CIPHERTEXT][SHA256(CIPHERTEXT)] from fin and writes plaintext to fout.
// It returns whether authentication matched.
func cbcDecryptStream(fin *os.File, fout *os.File, subkeys [64]word64) (bool, error) {
	// Determine file size to separate trailing 32-byte hash
	st, err := fin.Stat()
	if err != nil {
		return false, err
	}
	if st.Size() < int64(BLOCK_SIZE+32) {
		return false, fmt.Errorf("input too small")
	}
	payload := st.Size() - 32 // up to before hash

	// Read IV
	iv := make([]byte, BLOCK_SIZE)
	if _, err := io.ReadFull(fin, iv); err != nil {
		return false, err
	}

	// Read stored hash (at end)
	if _, err := fin.Seek(payload, io.SeekStart); err != nil {
		return false, err
	}
	storedHash := make([]byte, 32)
	if _, err := io.ReadFull(fin, storedHash); err != nil {
		return false, err
	}

	// Prepare to stream-decrypt ciphertext (between IV and payload end)
	if _, err := fin.Seek(BLOCK_SIZE, io.SeekStart); err != nil {
		return false, err
	}
	remaining := payload - BLOCK_SIZE
	if remaining <= 0 || (remaining%BLOCK_SIZE) != 0 {
		return false, fmt.Errorf("invalid ciphertext size")
	}

	prev := [BLOCK_SIZE]byte{}
	copy(prev[:], iv)

	hasher := sha256.New()

	reader := bufio.NewReader(io.LimitReader(fin, remaining))
	inbuf := make([]byte, READ_CHUNK)
	outbuf := make([]byte, READ_CHUNK)

	for remaining > 0 {
		toread := READ_CHUNK
		if int64(toread) > remaining {
			toread = int(remaining)
		}
		// align to BLOCK_SIZE
		toread -= (toread % BLOCK_SIZE)
		n, rerr := io.ReadFull(reader, inbuf[:toread])
		if rerr != nil && rerr != io.ErrUnexpectedEOF && rerr != io.EOF {
			return false, rerr
		}
		if n == 0 {
			break
		}

		// hash ciphertext
		if _, herr := hasher.Write(inbuf[:n]); herr != nil {
			return false, herr
		}

		// decrypt blocks
		for off := 0; off < n; off += BLOCK_SIZE {
			var cpy [BLOCK_SIZE]byte
			copy(cpy[:], inbuf[off:off+BLOCK_SIZE])
			inw := beBytesToWords(inbuf[off : off+BLOCK_SIZE])
			outw := gostdecrypt(inw, subkeys)
			beWordsToBytes(outw, outbuf[off:off+BLOCK_SIZE])
			// XOR with previous ciphertext (CBC)
			for i := 0; i < BLOCK_SIZE; i++ {
				outbuf[off+i] ^= prev[i]
			}
			copy(prev[:], cpy[:])
		}

		remaining -= int64(n)

		// If this is not the final read, write all outbuf; else, keep last block to unpad.
		if remaining > 0 {
			if _, werr := fout.Write(outbuf[:n]); werr != nil {
				return false, werr
			}
		} else {
			// Last chunk: remove PKCS#7 padding on its last block
			if n < BLOCK_SIZE {
				return false, fmt.Errorf("truncated final block")
			}
			keep := n - BLOCK_SIZE
			if keep > 0 {
				if _, werr := fout.Write(outbuf[:keep]); werr != nil {
					return false, werr
				}
			}
			lastblk := make([]byte, BLOCK_SIZE)
			copy(lastblk, outbuf[keep:n])
			unpadded, uerr := pkcs7Unpad(lastblk)
			if uerr != nil {
				return false, fmt.Errorf("invalid padding: %w", uerr)
			}
			if len(unpadded) > 0 {
				if _, werr := fout.Write(unpadded); werr != nil {
					return false, werr
				}
			}
		}
	}

	// Verify hash
	calcHash := hasher.Sum(nil)
	authOK := (len(calcHash) == 32 && len(storedHash) == 32 && string(calcHash) == string(storedHash))
	return authOK, nil
}

// =========================
//            MAIN
// =========================

func usage(prog string) {
	fmt.Fprintf(os.Stderr, "Usage: %s c|d <input_file>\n", filepath.Base(prog))
}

func main() {
	if len(os.Args) != 3 {
		usage(os.Args[0])
		os.Exit(1)
	}
	modeEncrypt := false
	switch os.Args[1] {
	case "c":
		modeEncrypt = true
	case "d":
		modeEncrypt = false
	default:
		usage(os.Args[0])
		os.Exit(1)
	}

	inpath := os.Args[2]
	var outpath string
	if modeEncrypt {
		outpath = makeOutputNameEncrypt(inpath)
	} else {
		outpath = makeOutputNameDecrypt(inpath)
	}

	// Open files
	fin, err := os.Open(inpath)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: cannot open input '%s': %v\n", inpath, err)
		os.Exit(1)
	}
	defer fin.Close()

	fout, err := os.Create(outpath)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: cannot create output '%s': %v\n", outpath, err)
		os.Exit(1)
	}
	defer func() {
		fout.Close()
	}()

	// Read password (not from CLI)
	password, err := promptPassword("Enter password: ")
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error reading password: %v\n", err)
		os.Remove(outpath)
		os.Exit(1)
	}

	// Init cipher tables and derive subkeys
	kboxinit()
	subkeys := deriveGOSTSubkeysFromPassword(password)

	// Zero password variable (best-effort)
	password = strings.Repeat("\x00", len(password))

	if modeEncrypt {
		if err := cbcEncryptStream(fin, fout, subkeys); err != nil {
			fmt.Fprintln(os.Stderr, "Operation failed due to an error.")
			_ = os.Remove(outpath) // best-effort remove incomplete output
			os.Exit(2)
		}
		fmt.Printf("Encryption completed. Output: %s\n", outpath)
	} else {
		authOK, err := cbcDecryptStream(fin, fout, subkeys)
		if err != nil {
			fmt.Fprintln(os.Stderr, "Operation failed due to an error.")
			_ = os.Remove(outpath) // best-effort remove incomplete output
			os.Exit(2)
		}
		fmt.Printf("Decryption completed. Output: %s\n", outpath)
		if authOK {
			fmt.Println("Authentication OK")
		} else {
			fmt.Println("Authentication FAILED")
		}
	}
}
