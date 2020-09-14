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

$counterexample
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
