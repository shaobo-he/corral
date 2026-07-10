function safe_for_add2(int) returns (bool);
axiom (forall y: int :: { safe_for_add2(y) } safe_for_add2(y) ==> y <= 2147483645);

function {:inline} $add.i64(i1: int, i2: int) returns (int) { (i1 + i2) }
function {:inline} $sub.i64(i1: int, i2: int) returns (int) { (i1 - i2) }
function {:inline} $sgt.i64(i1: int, i2: int) returns (int) { (if i1 > i2 then 1 else 0) }
function {:inline} $slt.i64(i1: int, i2: int) returns (int) { (if i1 < i2 then 1 else 0) }
function {:inline} $or.i1(i1: int, i2: int) returns (int) { (if i1 != 0 || i2 != 0 then 1 else 0) }
function {:inline} $zext.i1.i32(i1: int) returns (int) { i1 }

procedure __SMACK_check_overflow(flag: int);

implementation __SMACK_check_overflow(flag: int)
{
entry:
  assert {:overflow} flag == 0;
  return;
}

procedure main();

implementation main()
{
  var x: int;
  var y: int;
  var t: int;
  var sum2: int;
  var sum1: int;
  var hi2: int;
  var lo2: int;
  var raw2: int;
  var flag2: int;
  var hi1: int;
  var lo1: int;
  var raw1: int;
  var flag1: int;

entry:
  assume x <= 2147483645 || x <= 2147483645;
  t := x + 2;
  assert {:smack.check_id "ov.add2.high"} {:smack.check_kind "overflow"} t <= 2147483647;
  assert {:smack.check_id "ov.add1.high"} {:smack.check_kind "overflow"} x + 1 <= 2147483647;

  assume safe_for_add2(y);
  assume y >= -2147483647;
  sum2 := $add.i64(y, 2);
  hi2 := $sgt.i64(sum2, 2147483647);
  lo2 := $slt.i64(sum2, $sub.i64(0, 2147483648));
  raw2 := $or.i1(hi2, lo2);
  flag2 := $zext.i1.i32(raw2);
  call {:smack.check_id "ov.call.add2"} __SMACK_check_overflow(flag2);

  sum1 := $add.i64(y, 1);
  hi1 := $sgt.i64(sum1, 2147483647);
  lo1 := $slt.i64(sum1, $sub.i64(0, 2147483648));
  raw1 := $or.i1(hi1, lo1);
  flag1 := $zext.i1.i32(raw1);
  call {:smack.check_id "ov.call.add1"} __SMACK_check_overflow(flag1);
  return;
}
