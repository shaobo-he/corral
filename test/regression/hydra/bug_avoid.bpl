var g: int;
procedure {:entrypoint} main() {
  g := 0;
  if (*) { call a(); } else { call b(); }
}
procedure a() { assert true; }
procedure b() { assert g != 0; }
