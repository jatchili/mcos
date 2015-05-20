var SECURITY_PARAMS = {
	k: 60,	// k/2 entries per ticket; k <= 256 and must be even
	m: 80	// Size of Schnorr ZKP challenge; m <= 128 and must be a multiple of 4
}