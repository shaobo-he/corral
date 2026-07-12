// A buggy program under /smackDependencyAnalysis: the first overflow check is
// covered (rewritten to an assume) and the second one fails. This exercises
// counterexample trace mapping and printing through rewritten blocks, which
// crashed when traces were printed against the pass's output program.
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
  var y: int;
  var sumA: int;
  var hiA: int;
  var loA: int;
  var rawA: int;
  var flagA: int;
  var sumB: int;
  var hiB: int;
  var loB: int;
  var rawB: int;
  var flagB: int;

entry:
  assume y <= 2147483645;
  assume y >= -2147483650;

  // checkA: y + 2 stays in range given the assumes -> covered.
  sumA := $add.i64(y, 2);
  hiA := $sgt.i64(sumA, 2147483647);
  loA := $slt.i64(sumA, $sub.i64(0, 2147483648));
  rawA := $or.i1(hiA, loA);
  flagA := $zext.i1.i32(rawA);
  call {:smack.check_id "ov.call.A"} __SMACK_check_overflow(flagA);

  // checkB: y - 1 underflows at y = -2147483650 -> kept, and it fails.
  sumB := $sub.i64(y, 1);
  hiB := $sgt.i64(sumB, 2147483647);
  loB := $slt.i64(sumB, $sub.i64(0, 2147483648));
  rawB := $or.i1(hiB, loB);
  flagB := $zext.i1.i32(rawB);
  call {:smack.check_id "ov.call.B"} __SMACK_check_overflow(flagB);
  return;
}
