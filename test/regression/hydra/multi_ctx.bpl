procedure {:entrypoint} main() {
  call a();
  call b();
}
procedure a() { call shared(); }
procedure b() { call shared(); }
procedure shared() { assert true; }
