// A duplicate entry in a callee's modifies clause.
//
// Boogie 3.5.6's CallCmd.ComputeDesugaring builds a Dictionary keyed on each
// modified variable and so assumes the modifies clause has no duplicates; a
// duplicate makes it throw ArgumentException ("An item with the same key has
// already been added"). Boogie 2.9.1 rebuilt the modifies list from the
// inferred modset, so duplicates could never reach that code and upstream
// Corral verifies this program normally.
//
// corral runs with InferModifies=true, which disables the resolver's modifies
// check, so a duplicate written here survives parsing. Expect: True bug.

var g: int;
var h: int;

procedure callee();
  modifies g, h, g;
implementation callee()
{
  g := g + 1;
  h := h + 1;
}

procedure main();
  modifies g, h;
implementation main()
{
  g := 0;
  h := 0;
  call callee();
  assert g == 0;
}
