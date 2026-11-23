// Independent wire-image vectors. Run with Go >= 1.24.
package main

import (
	"bytes"
	"crypto/sha3"
	"fmt"
)

func hash(domain string, parts ...[]byte) []byte {
	h := sha3.NewCSHAKE256(nil, []byte(domain))
	for _, part := range parts {
		h.Write(part)
	}
	output := make([]byte, 32)
	h.Read(output)
	return output
}
func node(tag byte, parts ...[]byte) []byte {
	return hash("DREGG/PRIVATE-CELL/NODE/v2", append([][]byte{{tag}}, parts...)...)
}
func leaf(class, parameter, id byte) []byte {
	addr := []byte{id, 255}
	address := hash("DREGG/PRIVATE-CELL/ADDRESS/v1", addr)
	// 4 family/marker bits, 256 Nat.testBit bits, 256 address hash
	// bits, 4 zero padding bits. The fixture repeats one parameter octet.
	path := make([]byte, 65)
	path[0] = class << 4
	for i := 0; i < 256; i++ {
		path[(4+i)/8] |= (parameter >> uint(i%8) & 1) << uint(7-(4+i)%8)
		path[(260+i)/8] |= (address[i/8] >> uint(7-i%8) & 1) << uint(7-(260+i)%8)
	}
	content := hash("DREGG/PRIVATE-CELL/CONTENT/v1", []byte{2, 255}, addr, []byte{id + 10, 255})
	return node(0, path, content)
}
func main() {
	body, atoms, code := leaf(6, 0, 1), leaf(7, 7, 2), leaf(4, 0, 3)
	empty := node(2)
	// The three class prefixes are 0110, 0111 and 0100.
	inner := node(1, node(1, empty, node(1, code, node(1, body, atoms))), empty)
	wire := append([]byte("DREGG/STORE\x03"), bytes.Repeat([]byte{9}, 32)...)
	frame := append([]byte{48, 255, 1, 255, 44, 255}, wire...)
	frame = append(frame, 41, 255, 4, 255, 's', 'e', 'a', 't', 45, 1, 255)
	outer := hash("DREGG/PRIVATE-CELL/OUTER/v2", frame, bytes.Repeat([]byte{17}, 32), inner)
	fmt.Printf("private_inner=%x\nprivate_outer=%x\n", inner, outer)
	path := bytes.Repeat([]byte{0x54}, 65)
	path[64] = 0x40
	d := node(0, path, bytes.Repeat([]byte{42}, 32))
	for i := 515; i >= 0; i-- {
		sibling := bytes.Repeat([]byte{byte(i)}, 32)
		if path[i/8]&(128>>uint(i%8)) != 0 {
			d = node(1, sibling, d)
		} else {
			d = node(1, d, sibling)
		}
	}
	fmt.Printf("public_full_depth_root=%x\n", d)
}
