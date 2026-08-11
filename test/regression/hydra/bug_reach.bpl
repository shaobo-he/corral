var g: int;
procedure {:entrypoint} main() {
  g := 0;
  if (*) { call a(); } else { call b(); }
}
procedure a() { assert g != 0; }
procedure b() { assert true; }
