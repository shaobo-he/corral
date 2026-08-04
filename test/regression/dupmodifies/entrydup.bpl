// As dup.bpl, but the duplicate is on the entry procedure.
//
// The entry point is not exempt: corral's instrumentation wraps main in a
// caller, so main's own modifies clause is desugared through the same
// CallCmd path. Expect: True bug.

var g: int;
var h: int;

procedure callee();
  modifies g, h;
implementation callee()
{
  g := g + 1;
  h := h + 1;
}

procedure main();
  modifies g, h, g;
implementation main()
{
  g := 0;
  h := 0;
  call callee();
  assert g == 0;
}
