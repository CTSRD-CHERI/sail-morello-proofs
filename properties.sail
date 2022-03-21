infixr 1 -->

type operator -->('p: Bool, 'q: Bool) -> Bool = not('p) | 'q
val operator --> : forall ('p 'q: Bool). (bool('p), bool('q)) -> bool('p --> 'q)
function operator --> (p, q) = not_bool(p) | q

infix 1 <-->

type operator <-->('p: Bool, 'q: Bool) -> Bool = ('p --> 'q) & ('q --> 'p)
val operator <--> : forall ('p 'q: Bool). (bool('p), bool('q)) -> bool('p <--> 'q)
function operator <--> (p, q) = (p --> q) & (q --> p)

overload not = {not_bool, not_vec}

$property
function propCapSetValueBoundsEq(c : Capability, v' : bits(64)) -> bool = {
  let c' = CapSetValue(c, v');
  let (origBase, origLimit, origValid) = CapGetBounds(c);
  let (newBase, newLimit, newValid) = CapGetBounds(c');
  CapIsTagSet(c') --> (origBase == newBase & origLimit == newLimit)
}

$property
function propCapAddBoundsEq(c : Capability, v' : bits(64)) -> bool = {
  let c' = CapAdd(c, v');
  let (origBase, origLimit, origValid) = CapGetBounds(c);
  let (newBase, newLimit, newValid) = CapGetBounds(c');
  CapIsTagSet(c') --> (origBase == newBase & origLimit == newLimit)
}

// let initial_cap : Capability = 0b111111111111111111100000000000000000000000000000100000000000001010000000000000000000000000000000000000000000000000000000000000000

$property
function propCapSetBoundsMono(c : Capability, req_len : bits(64), exact : bool) -> bool = {
  let req_len = ZeroExtend(req_len, 65);
  let c' = CapSetBounds(c, req_len, exact);
  let (origBase, origLimit, origValid) = CapGetBounds(c);
  let (newBase, newLimit, newValid) = CapGetBounds(c');
  let requestSensible = CapUnsignedLessThanOrEqual(origLimit, CAP_BOUND_MAX);
  // let requestSatisfied = CapUnsignedLessThanOrEqual(newBase, reqBase) & CapUnsignedLessThanOrEqual(reqLimit, newLimit);
  let boundsMonotonic = CapUnsignedLessThanOrEqual(origBase, newBase) & CapUnsignedLessThanOrEqual(newLimit, origLimit);
  let expMonotonic = CapGetExponent(c') <= CapGetExponent(c);
  (CapIsTagSet(c') & requestSensible) --> ( /*requestSatisfied &*/ boundsMonotonic & expMonotonic)
}

$property
function propCapSetBoundsMaxExp(c : Capability, req_len : bits(65), exact : bool) -> bool = {
  if UInt(req_len) <= pow2(64) then {
    let c' = CapSetBounds(c, req_len, exact);
    CapGetExponent(c') <= CAP_MAX_EXPONENT
  } else true
}

$property
function propCapSetFlagsBoundsEq(c : Capability, flags : bits(8)) -> bool = {
  let newvalue = flags @ (CapGetValue(c)[55..0]);
  let c' = CapSetFlags(c, newvalue);
  let (origBase, origLimit, origValid) = CapGetBounds(c);
  let (newBase, newLimit, newValid) = CapGetBounds(c');
  CapIsTagSet(c') --> (origBase == newBase & origLimit == newLimit)
}

$property
function propSetLSBsMono(c : Capability, bits : bits(CAP_MW - 3)) -> bool = {
  let c' = [c with (CAP_MW - 4) .. 0 = bits];
  let (origBase, origLimit, origValid) = CapGetBounds(c);
  let (newBase, newLimit, newValid) = CapGetBounds(c');
  (origBase == newBase & origLimit == newLimit)
}

function canonicalBounds(c) : Capability -> bool = {
  let bot = CapGetBottom(c);
  let top = CapGetTop(c);
  let exp = CapGetExponent(c);
  if CapIsExponentOutOfRange(c) | exp == CAP_MAX_ENCODEABLE_EXPONENT then {
    false
  } else if exp == CAP_MAX_EXPONENT then {
    top[CAP_MW - 1] == bitzero & bot[CAP_MW - 1 .. CAP_MW - 2] == 0b00
  } else if exp == (CAP_MAX_EXPONENT - 1) then {
    bot[CAP_MW - 1] == bitzero
  } else {
    true
  }
}

$property
function propCapSetBoundsCanonical(c : Capability, req_len : bits(65), exact : bool) -> bool = {
  if UInt(req_len) <= pow2(64) then {
    let c' = CapSetBounds(c, req_len, exact);
    let newBase = UInt(CapGetValue(c));
    let newTop = newBase + UInt(req_len);
    let requestSensible = newTop <= pow2(CAP_VALUE_NUM_BITS);
    requestSensible --> canonicalBounds(c')
  } else true
}

$property
function propCapBaseLeqLimit(c : Capability) -> bool = {
  let (base, limit, valid) = CapGetBounds(c);
  canonicalBounds(c) --> (UInt(base) <= UInt(limit))
}

$property
function propBuildCapDerivable(data : Capability, key : Capability) -> bool = {
  let unsealed_data = if CapIsSealed(data) then CapUnseal(data) else data;
  let (base, limit, valid) = CapGetBounds(data);
  let length = limit - base;
  let (_, olimit, _) = CapGetBounds(key);
  let from_large = not(CapBoundsUsesValue(CapGetExponent(key)));
  let to_small = CapBoundsUsesValue(CapGetExponent(data));
  let key_flags_ok = from_large | (CapGetValue(key)[CAP_FLAGS_LO_BIT - 1] == base[CAP_FLAGS_LO_BIT - 1]);
  let base_flags_ok = (to_small --> CapBoundsAddress(base[63 .. 0]) == base[63 .. 0]);
  let addr_flags_ok = (to_small --> CapGetValue(data)[CAP_FLAGS_LO_BIT - 1] == base[CAP_FLAGS_LO_BIT - 1]);
  let bounds_ok = canonicalBounds(data) & key_flags_ok & base_flags_ok & addr_flags_ok & CapUnsignedLessThanOrEqual(length, CAP_BOUND_MAX);
  let cap_checks_pass = CapIsTagSet(key) & not(CapIsSealed(key)) & CapIsSubSetOf(data, key);
  if (cap_checks_pass & bounds_ok) then {
    // If the checks succeed, then the output of BUILD is equal to the result of rederivation from the tagged capability
    let perms = ZeroExtend(CapGetPermissions(data), 64);
    let derivation1 = CapSetValue(key, base[63 .. 0]);
    let derivation2 = CapSetBounds(derivation1, length, true);
    let derivation3 = CapSetValue(derivation2, CapGetValue(data));
    let derivation_result = CapClearPerms(derivation3, not_vec(perms));
    (CapWithTagSet(unsealed_data) == derivation_result)
  } else {
    // If any of the above checks fail, we don't guarantee anything about the result
    true
  }
}

/* Setting bounds to a length smaller than 2^(CAP_MW-2) is always exact */

$property
function propCapSetBoundsSmallExact(c : Capability, len : bits(64)) -> bool = {
  let c' = CapSetBounds(c, 0b0 @ len, true);
  /* The expected new base is the sign-extended capability value with
   * normalised flags (top 8 bits), because the exponent will be zero */
  let expectedBase = 0b0 @ CapBoundsAddress(CapGetValue(c));
  /* The expected new top is exactly len above the new base */
  let expectedTop = expectedBase + (0b0 @ len);
  let (newBase, newTop, _) = CapGetBounds(c');
  let lenSmall = (UInt(len) < pow2(CAP_MW - 2));
  let exact = (newBase == expectedBase & newTop == expectedTop);
  lenSmall --> exact
}

function CapGetRepresentableLength(len : bits(64)) -> bits(64) = {
  let mask = CapGetRepresentableMask(len);
  (len + not(mask)) & mask
}

/* A help function defining how CapSetBounds normalises the top 8 bits of the base */

val normaliseBaseFlags : forall 'oldExp 'newExp, 'oldExp >= 0 & 'newExp >= 0. (bits(64), int('oldExp), int('newExp)) -> bits(64)

function normaliseBaseFlags(base, oldExp, newExp) = {
  if CapBoundsUsesValue(oldExp) then {
    /* If the capability originally has a small exponent, then all 8 bits will be normalised */
    return CapBoundsAddress(base);
  } else if (newExp + CAP_MW < CAP_FLAGS_LO_BIT) then {
    /* Same if the mantissa is completely below the top byte */
    return CapBoundsAddress(base);
  } else if (newExp + CAP_MW >= CAP_VALUE_NUM_BITS) then {
    /* If the mantissa covers the top byte, those bits will come from the mantissa unchanged */
    return base;
  } else {
    /* If there is a partial overlap between mantissa and top byte, then the
     * mantissa bits will be unchanged, others will be normalised */
    let numTopBits = CAP_VALUE_NUM_BITS - newExp - CAP_MW;
    let topBits = (if base[CAP_FLAGS_LO_BIT - 1] == bitone then Ones(numTopBits) else Zeros(numTopBits));
    return topBits @ base[CAP_VALUE_NUM_BITS - numTopBits - 1 .. 0];
  }
}

/* Setting bounds aligned and padded using RRMASK/RRLEN will be exact, modulo
 * flag bits normalisation */
$property
function propRepresentableSetBoundsExact(c : Capability, len : bits(64)) -> bool = {
  let c' = CapSetBounds(c, 0b0 @ len, true);
  let repMask = CapGetRepresentableMask(len);
  let repLen = CapGetRepresentableLength(len);
  let base = CapGetValue(c);
  let (newBase, newTop, _) = CapGetBounds(c');

  /* Assume that aligned and padded bounds */
  let baseAligned = ((base & repMask) == base);
  let lenPadded = (len == repLen);

  /* In that case, the low 56 bits of base and top are guaranteed to be exactly as requested */
  let top : bits(65) = (0b0 @ base) + (0b0 @ len);
  let exact56 = (newBase[55 .. 0] == base[55 .. 0] & newTop[55 .. 0] == top[55 .. 0]);

  /* The top 8 bits of VAs are reserved for flag bits, so the top byte of the
   * base will be normalised as defined in the above helper function, provided
   * that the flags check in CapSetBounds succeeds (the tag will be cleared if
   * it doesn't). */
  let expectedBase : bits(65) = 0b0 @ (normaliseBaseFlags(base, CapGetExponent(c), CapGetExponent(c')));
  let expectedTop : bits(65) = expectedBase + (0b0 @ len);
  let exactFlags = (newBase == expectedBase) & (newTop == expectedTop);

  /* For aligned and padded bounds, CapSetBounds will not clear the tag due to
   * inexactness, so the tag depends only on the flags and bounds checks
   * performed by CapSetBounds, replicated here. */
  let fromLarge = not(CapBoundsUsesValue(CapGetExponent(c)));
  let toSmall = CapBoundsUsesValue(CapGetExponent(c'));
  let flagsCheckPassed = (fromLarge & toSmall --> SignExtend(base[CAP_FLAGS_LO_BIT - 1 .. 0], 64) == base);

  let reqBase = 0b0 @ (if CapBoundsUsesValue(CapGetExponent(c)) then CapBoundsAddress(base) else base);
  let reqTop = reqBase + (0b0 @ len);
  let (origBase, origTop, origValid) = CapGetBounds(c);
  let boundsCheckPassed = (CapUnsignedGreaterThanOrEqual(reqBase, origBase) & CapUnsignedLessThanOrEqual(reqTop, origTop) & origValid);

  let tagCorrect = (CapIsTagSet(c') <--> CapIsTagSet(c) & flagsCheckPassed & boundsCheckPassed);

  /* Putting it all together: */
  (baseAligned & lenPadded) --> (tagCorrect & exact56 & (flagsCheckPassed --> exactFlags))
}

/* RRLEN is not idempotent on Morello */

$counterexample
function propRepresentableLengthIdempotent(len : bits(64)) -> bool = {
  let repLen = CapGetRepresentableLength(len);
  CapGetRepresentableLength(repLen) == repLen
}

/* CRRL is idempotent on CHERI-RISC-V, however, due to a change to the
 * calculation of the alignment mask, using Zeros() instead of (Ones() - len)
 * as the test base. */

val CapGetRepresentableMaskAlt : bits(CAP_VALUE_NUM_BITS) -> bits(CAP_VALUE_NUM_BITS) effect {escape, undef}

function CapGetRepresentableMaskAlt(len) = {
    c : bits(129) = CapNull();
    let test_base : bits(CAP_VALUE_NUM_BITS) = Zeros(CAP_VALUE_NUM_BITS);
    let test_length : bits(CAP_LENGTH_NUM_BITS) = ZeroExtend(len, CAP_LENGTH_NUM_BITS);
    c[CAP_VALUE_HI_BIT .. CAP_VALUE_LO_BIT] = test_base;
    let c : bits(129) = CapSetBounds(c, test_length, false);
    exp1 : int = 0;
    if CapIsInternalExponent(c) then {
        exp1 = CapGetExponent(c) + 3
    };
    let 'exp1 = exp1;
    assert(constraint(64 - '_exp1 >= 0));
    assert(constraint('_exp1 >= 0));
    return(Ones(CAP_VALUE_NUM_BITS - exp1) @ Zeros(exp1))
}

function CapGetRepresentableLengthAlt(len : bits(64)) -> bits(64) = {
  let mask = CapGetRepresentableMaskAlt(len);
  (len + not(mask)) & mask
}

/* With this alternative definition, RRLEN is idempotent */

$property
function propRepresentableLengthAltIdempotent(len : bits(64)) -> bool = {
  let repLen = CapGetRepresentableLengthAlt(len);
  CapGetRepresentableLengthAlt(repLen) == repLen
}

/* RRMASK(RRLEN(len)) == RRMASK(len) with the alternative mask calculation,
 * unless there is a length overflow (RRLEN returns zero for lengths that would
 * get rounded up to 2^64) */

$property
function propRepresentableMaskLengthAbsorb(len : bits(64)) -> bool = {
  let repLen = CapGetRepresentableLengthAlt(len);
  let noLenOverflow = (UInt(repLen) == 0 --> UInt(len) == 0);
  noLenOverflow --> (CapGetRepresentableMaskAlt(repLen) == CapGetRepresentableMaskAlt(len))
}
