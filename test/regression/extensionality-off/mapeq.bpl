// The program from extensionality-auto, run with /noArrayExtensionality. With
// extensionality off the prover cannot conclude `b == c` from pointwise facts,
// so corral reports the assertion as failing. This pins that the flag really
// keeps extensionality off; the program itself is correct.
procedure main()
{
  var a, b, c: [int]int;
  var i, j, x, y: int;

  assume i != j;
  b := a[i := x][j := y];
  c := a[j := y][i := x];
  assert b == c;
}
