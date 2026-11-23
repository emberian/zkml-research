// Independent Minidregg outer-hash vector. Run with Go >= 1.24.
package main

import (
	"crypto/sha3"
	"encoding/hex"
	"fmt"
)

func main() {
	// NativeDocWriteFixtureData.lean:29, first 44-byte DREGG/STORE frame.
	wire, err := hex.DecodeString("44524547472f53544f5245036b7852d67118b7c51346d5ee0e6e0e2a10ef316e4a7501098dc7342683900bdc")
	if err != nil {
		panic(err)
	}
	// Hand-encoded StreamCodec.nat base 255, 0xff terminator.
	// kindCtx = (1,wire); cell = "seat"; version = 300 = 45 + 255.
	frame := append([]byte{48, 255, 1, 255, 44, 255}, wire...)
	frame = append(frame, 41, 255, 4, 255, 's', 'e', 'a', 't', 45, 1, 255)
	// custodyFrame has 9 bytes and secret has 32 bytes.
	preimage := append([]byte{}, frame...)
	for i := 0; i < 64; i++ {
		preimage = append(preimage, byte(i))
	}
	h := sha3.NewCSHAKE256(nil, []byte("DREGG/PRIVATE-CELL/OUTER/v2"))
	h.Write(preimage)
	var digest [32]byte
	h.Read(digest[:])
	fmt.Printf("outer_frame=%x\nouter_root=%x\n", frame, digest)
}
