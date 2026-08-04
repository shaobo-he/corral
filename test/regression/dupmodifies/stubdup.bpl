// Makes the CONTENT of a deduplicated modifies clause observable.
//
// dup.bpl and entrydup.bpl only check that a duplicate modifies entry no
// longer crashes CallCmd.ComputeDesugaring. In both of those every callee has
// a body, so stratified inlining inlines it and the modifies clause never
// decides the verdict -- a regression that over-prunes the clause would leave
// them green.
//
// Here `stub` has no implementation, so corral cannot inline it and must
// instead havoc its modifies clause at the call site. `h` is therefore unknown
// after the call and the assertion can fail: expect True bug.
//
// The point is what happens if the normalisation in BoogieUtil.DoModSetAnalysis
// ever over-prunes. It keys on variable NAME rather than identity, so a coarser
// key -- or keeping only the first entry -- would drop `h` from stub's clause,
// the call would no longer havoc `h`, and corral would report "Program has no
// bugs". That is a missed bug, and this test is the one that would catch it.

var g: int;
var h: int;

// no implementation: the modifies clause is all corral has to go on
procedure stub();
  modifies g, h, g;

procedure main();
  modifies g, h;
implementation main()
{
  g := 0;
  h := 0;
  call stub();
  assert h == 0;
}
