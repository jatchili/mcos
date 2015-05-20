/*
Dependencies:

http://www-cs-students.stanford.edu/~tjw/jsbn/
	jsbn.js
	jsbn2.js

https://github.com/bitwiseshiftleft/sjcl
	sjcl.js
	sjcl-bn.js

Protocol/identity files:
	SECURITY_PARAMS.js (Everyone)
	GROUP_PARAMS.js (Everyone)
	ISSUER_KEY.js (Everyone, but only Issuer has private key)
	POLL_PARAM.js (Poll-runner only)
	USER_KEY.js (User only)
*/

// Setup for NodeJS only
if (typeof module !== "undefined" && module.exports) {
	var fs = require("fs");
	var vm = require('vm');
	var includeInThisContext = function(path) {
	    var code = fs.readFileSync(path);
	    vm.runInThisContext(code, path);
	}.bind(this);
	BigInteger = require("./external/jsbn-node.js");
	sjcl = require("./node_modules/sjcl");
	includeInThisContext("./external/sjcl-bn.js");
	includeInThisContext("./config/SECURITY_PARAMS.js");
	includeInThisContext("./config/GROUP_PARAMS.js");
	includeInThisContext("./config/ISSUER_KEY.js");
	includeInThisContext("./config/POLL_PARAM.js");
	includeInThisContext("./config/USER_KEY.js");
}

var p = new BigInteger(GROUP_PARAMS.p, 16);
var q = new BigInteger(GROUP_PARAMS.q, 16);
var g = new BigInteger(GROUP_PARAMS.g, 16);

var n = new BigInteger(ISSUER_KEY.n, 16);
var e = new BigInteger(ISSUER_KEY.e, 16);
var d;
if (ISSUER_KEY.d) {
	d = new BigInteger(ISSUER_KEY.e, 16);
}

var k = SECURITY_PARAMS.k;
var m = SECURITY_PARAMS.m;

var userSecret = new BigInteger(USER_KEY.secret, 16);
var userPublic = new BigInteger(USER_KEY.pub, 16);



// Generic helper functions

/* Pseudorandom 256-bit BigInteger.
Uses concatentation of hex strings, which is a bit strange,
but okay if it's consistent for all parties. */
function randomFromSeedAndCounter(seedString, counter) {
	return new BigInteger(
		sjcl.bn.fromBits(
			sjcl.hash.sha256.hash(seedString+","+counter)
		).toString(16).slice(2), 16);
}

/* Operations involving a boolean array ("Bar") */
function hexToBar(hex) {
	var o = [];
	for (var i=0; i<hex.length; i++) {
		var c = hex[i];
		var b = parseInt(c,16).toString(2);
		while (b.length < 4) {
			b = "0" + b;
		}
		for (var j=0; j<4; j++) {
			if (b[j] === "1") {
				o.push(true);
			} else {
				o.push(false);
			}
		}
	}
	return o;
}
function barToHex(bar) {
	while (bar.length % 4 !== 0) {
		bar.unshift(false);
	}
	var hex = "";
	for (var i=0; i<bar.length; i+=4) {
		var bitString =
			(bar[i  ] ? "1" : "0") +
			(bar[i+1] ? "1" : "0") + 
			(bar[i+2] ? "1" : "0") +
			(bar[i+3] ? "1" : "0");
		var hexChar = parseInt(bitString,2).toString(16);
		hex += hexChar;
	}
	return hex;
}
function numberOfOnes(bar) {
	var r = 0;
	for (var i=0; i<bar.length; i++) {
		if (bar[i]) r++;
	}
	return r;
}

/* Deterministically generate a Bar of size "size", with half being true and half false.
"size" must be even, and no greater than 256. */
function generateHalfAndHalfBar(size, seedString) {
	var bar = hexToBar(sjcl.bn.fromBits(sjcl.hash.sha256.hash(seedString)).toString(16).slice(2));
	while (bar.length < 256) {
		bar.unshift(false);
	}
	bar = bar.slice(256-size);
	var ones = numberOfOnes(bar);
	var counter = 0;
	while (ones !== size/2) {
		var position = ((sjcl.hash.sha256.hash(seedString+""+counter)[0] % size) + size) % size;
		//console.log(position);
		if (ones < size/2) { // flick bits on
			bar[position] = true;
		} else { // flick bits off
			bar[position] = false;
		}
		ones = numberOfOnes(bar);
		counter++;
	}
	return bar;
}

/* (Hash mod n) of and ordered pair of (BigIntegers mod p).
(Again, uses hex strings) */
function computeEntryHash(yri, gri) {
	var yriString = yri.toString(16);
	var griString = gri.toString(16);
	return new BigInteger(
		sjcl.bn.fromBits(
			sjcl.hash.sha256.hash(yriString+","+griString)
		).toString(16).slice(2), 16
	).mod(n);
}




// Phase 1: Obtaining a voter-ticket

/* Create a "double voter-ticket", which contains twice as many entries as required,
so that half can be discarding during the Cut-and-Choose operation. If masterSeedString
is provided, generation is deterministic. */
function generateDVT(masterSeedString) {
	var providedSeed = !!masterSeedString;
	if (!providedSeed) {
		masterSeedString = sjcl.codec.hex.fromBits(sjcl.random.randomWords(8));
	}
	var entries = [];
	for (var i=0; i<k; i++) {
		var ri = randomFromSeedAndCounter(masterSeedString, i);
		var yri = userPublic.modPow(ri, p);
		var gri = g.modPow(ri, p);
		entries.push([yri, gri]);
	}
	var result = {entries: entries};
	result.masterSeedString = masterSeedString;
	return result;
}

/* Create a (blinder, blinded-signature-request) pair for the DVT. (Non-deterministic) */
function generateDVTSR(dvt) {
	var blindedHashes = [];
	var blinders = [];
	for (var i=0; i<dvt.entries.length; i++) {
		var entry = dvt.entries[i];
		var entryHash = computeEntryHash(entry[0], entry[1]);
		var blinder = new BigInteger(
			sjcl.bn.fromBits(
				sjcl.random.randomWords(8)
			).toString(16).slice(2),16
		).mod(n);
		var blinderToTheE = blinder.modPow(e, n);
		var blindedHash = blinderToTheE.multiply(entryHash).mod(n);
		blindedHashes.push(blindedHash);
		blinders.push(blinder);
	}
	return {
		blinders: blinders,
		blindedHashes: blindedHashes
	};
}

/* Generate a random challenge vector (CV) for Cut-and-Choose */
function randomCV() {
	return generateHalfAndHalfBar(k, sjcl.codec.hex.fromBits(sjcl.random.randomWords(8)));
}

/* Alternatively, given a list of blinded hashes, generate a CV */
function cvFromBlindedHashes(bhs) {
	var kk = bhs.length;
	var concatenation = "";
	for (var i=0; i<kk; i++) {
		concatenation += (bhs[i].toString(16));
	}
	return generateHalfAndHalfBar(kk, concatenation);
}

/* Answer the Cut-and-Choose challenge, encoding into hex for transmission. */
function answerChallenge(dvt, dvtsr, cv) {
	var answerRandoms = [];
	var answerBlinders = [];
	for (var i=0; i<cv.length; i++) {
		if (cv[i]) {
			answerRandoms.push(randomFromSeedAndCounter(dvt.masterSeedString, i).toString(16));
			answerBlinders.push(dvtsr.blinders[i].toString(16));
		}
	}
	return {
		randoms: answerRandoms,
		blinders: answerBlinders
	};
}

/* Check to see if that answer is correct, given the user's pubkey y. */
function verifyAnswer(answer, blindedHashes, cv, y) {
	if (answer.randoms.length !== k/2 || answer.blinders.length !== k/2) {
		return false;
	}
	var t = 0;
	for (var i=0; i<cv.length; i++) {
		if (cv[i]) {
			ri = new BigInteger(answer.randoms[t],16);
			blinder = new BigInteger(answer.blinders[t],16);
			t++;
			yri = y.modPow(ri, p);
			gri = g.modPow(ri, p);
			entryHash = computeEntryHash(yri, gri);
			blinderToTheE = blinder.modPow(e, n);
			blindedHash = blinderToTheE.multiply(entryHash).mod(n);
			if (!(blindedHashes[i].equals(blindedHash))) {
				return false;
			}
		}
	}
	return true;
}

/* Sign the product of the remaining k/2 hashes, i.e. where cv[i] is false. */
function sign(blindedHashes, cv) {
	var product = new BigInteger("1", 16);
	for (var i=0; i<cv.length; i++) {
		if (!cv[i]) {
			product = product.multiply(blindedHashes[i]).mod(n);
		}
	}
	// The following is the only line that uses d;
	// it should only ever be called by the Issuer.
	// Therefore, it's okay if d is undefined for everyone else.
	return product.modPow(d, n);
}

/* Remove the blinding from the blinded signature. */
function unblind(blindedSignature, blinders, cv) {
	var blinderProduct = new BigInteger("1", 16);
	for (var i=0; i<cv.length; i++) {
		if (!cv[i]) {
			blinderProduct = blinderProduct.multiply(blinders[i]).mod(n);
		}
	}
	var unblinder = blinderProduct.modInverse(n);
	return blindedSignature.multiply(unblinder).mod(n);
}




// Phase 2: Voting


/* Expand the abbreviated ticket, and encode it in hex for transmission */
function presentTicket(abbreviatedTicket) {
	var signature = abbreviatedTicket[0];
	var masterSeedString = abbreviatedTicket[1];
	var cv = hexToBar(abbreviatedTicket[2]);
	while (cv.length < k) {
		cv.unshift(false);
	}
	var dvt = generateDVT(masterSeedString);
	var entries = [];
	for (var i=0; i<k; i++) {
		if (!cv[i]) {
			entries.push([
				dvt.entries[i][0].toString(16),
				dvt.entries[i][1].toString(16)
			]);
		}
	}
	return {
		signature: signature,
		entries: entries
	};
}

/* Validate the signature on the presented ticket.
If it's valid, return the list of entries, as BigIntegers. */
function validateSignature(presentedTicket) {
	var hashProduct = new BigInteger("1",16);
	var entries = [];
	for (var i=0; i<presentedTicket.entries.length; i++) {
		var entry = presentedTicket.entries[i];
		var yri = new BigInteger(entry[0], 16);
		var gri = new BigInteger(entry[1], 16);
		var entryHash = computeEntryHash(yri, gri);
		entries.push([yri, gri]);
		hashProduct = hashProduct.multiply(entryHash).mod(n);
	}
	var signature = new BigInteger(presentedTicket.signature, 16);
	var validation = signature.modPow(e, n);
	if (validation.equals(hashProduct)) {
		return entries;
	} else {
		return false;
	}
}

/* Prepare the "allEntries" list, which is an array of all the
entries in the ticket as BigIntegers, plus the required
[pollGen^userSecret, pollGen] entry. */
function prepareAllEntries(entries, pollGen, secret) {
	var allEntries = [[pollGen.modPow(secret,p), pollGen]];
	for (var i=0; i<entries.length; i++) {
		entry = [
			new BigInteger(entries[i][0], 16),
			new BigInteger(entries[i][1], 16)
		];
		allEntries.push(entry);
	}
	return allEntries;
}

/* Generate the Schnorr ZKP commitment (non-deterministic). */
function schnorrZKPCommitment(allEntries) {
	var commitments = [];
	var random = new BigInteger(sjcl.bn.fromBits(sjcl.random.randomWords(64)).toString(16).slice(2),16).mod(p);
	for (var i=0; i<allEntries.length; i++) {
		var gri = allEntries[i][1];
		var commitment = gri.modPow(random, p);
		commitments.push(commitment);
	}
	return {
		commitments: commitments,
		random: random
	};
}

/* Generate a challenge for the ZKP */
function randomChallenge() {
	var r = new BigInteger(sjcl.bn.fromBits(sjcl.random.randomWords(4)).toString(16).slice(2),16);
	var modulus = "1";
	for (var i=0; i<m; i+=4) {
		modulus += "0";
	}
	return r.mod(new BigInteger(modulus,16));
}

/* Alternatively, generate the challenge deterministically, to make the proof non-interactive. */
function challengeFromSignature(hexSig) {
	var trimmedSig = new BigInteger(hexSig,16).toString(16);
	var r = new BigInteger(sjcl.bn.fromBits(sjcl.hash.sha256.hash(trimmedSig)).toString(16).slice(2),16);
	var modulus = "1";
	for (var i=0; i<m; i+=4) {
		modulus += "0";
	}
	return r.mod(new BigInteger(modulus,16));
}

/* Answer the challenge. */
function schnorrZKPAnswer(random, challenge, alpha) {
	return random.subtract(challenge.multiply(alpha));
}

/* Verify the answer. */
function verifyZKP(pollGen, allEntries, commitments, challenge, answer) {
	if (!(allEntries[0][1].equals(pollGen))) {
		return false;
	}
	for (var i=0; i<allEntries.length; i++) {
		var entry = allEntries[i];
		var yri = entry[0];
		var gri = entry[1];
		var gsyc = gri.modPow(answer, p).multiply(yri.modPow(challenge,p)).mod(p);
		if (!(gsyc.equals(commitments[i]))) {
			return false;
		}
	}
	return true;
}





// Test functions

function ticketTest() {
	var start = new Date();
	// User:
	var dvt = generateDVT();
	var dvtsr = generateDVTSR(dvt);

	var vtRequest = {
		blindedHashes: dvtsr.blindedHashes,
		//answer: answer,
		publicKey: userPublic
	};

	// Issuer:
	var cv = randomCV();

	// User:
	var answer = answerChallenge(dvt, dvtsr, cv);
	var blinders = dvtsr.blinders;

	// Issuer:
	var blindedSignature; // Sent to user
	if (vtRequest.blindedHashes.length !== k) {
		return;
	}
	if (verifyAnswer(answer, vtRequest.blindedHashes, cv, vtRequest.publicKey)) {
		blindedSignature = sign(vtRequest.blindedHashes, cv);
	} else {
		return;
	}

	// User:
	var signature = unblind(blindedSignature, blinders, cv);
	var cvAsHex = barToHex(cv);
	var result = [
		signature.toString(16),
		dvt.masterSeedString,
		cvAsHex
	];
	//console.log(result);
	console.log("ticketTest took", new Date() - start, "milliseconds");
	return result;
}


var exampleTicket = [
	"17475b4c67385f289eec46594a3ba6825fa01ed26a2d2c1f0cd12052025e95cd075b3eefefd238cc28d26726e3d27edd7cc01362e631f2627d8669008e83b12e2b34f318cc8fecc051fa41a4a901d3f39b2d12b6bea5e0607296c7106792d59a247aa53108a2a1bd5d89b50b520b7d462fda9af62764398d1b004f7d319df83ca11d69611a37c46d41cc39a9d9df6afe817bbb3103aaefaa51ff866abd9ec86225cb873476290182dbf0d949906f9e97c5138dc9af913d3c0f8895109b5ec7ce05f438f3bfdee3e0c6261d724a2050cf22914d0ff9a72896975f72a037305c420f47f9e59961d1fe7c9d3e63ef90aee5cad2b89306a5640b275e61ceac8f4646",
	"d2139c7612e3aa3ad3faf9d2d1404fc1884f9995b8b117fbc81fd9017fc75df4",
	"4b9b2e38a3"
];

function voteTest(ticket) {
	if (!ticket) {
		ticket = exampleTicket;
	}
	var start = new Date();
	var f = new BigInteger(POLL_PARAM.f,16);

	var pt = presentTicket(ticket);
	var allEntries = prepareAllEntries(pt.entries, f, userSecret);
	var zkp1 = schnorrZKPCommitment(allEntries);
	var commitments = zkp1.commitments;

	var challenge = challengeFromSignature(pt.signature);
	var zkpAnswer = schnorrZKPAnswer(zkp1.random, challenge, userSecret);
	verifyZKP(f, allEntries, commitments, challenge, zkpAnswer);
	console.log("voteTest took", new Date() - start, "milliseconds");
}


function completeTest() {
	var start = new Date();
	var ticket = ticketTest();
	voteTest(ticket);
	console.log("completeTest took", new Date() - start, "milliseconds");
}

function twentyTests() {
	for (var i=0; i<20; i++) {
		ticketTest();
	}
	for (var i=0; i<20; i++) {
		voteTest();
	}
}


if (typeof module !== "undefined" && module.exports) {
	module.exports = {
		ticketTest: ticketTest,
		voteTest: voteTest,
		completeTest: completeTest,
		twentyTests: twentyTests
	};
}