procedure __SMACK_check_overflow(flag: bv32);

implementation __SMACK_check_overflow(flag: bv32)
{
entry:
  assert {:overflow} flag == 0bv32;
  return;
}

procedure main();

implementation main()
{
  var flag: bv32;

entry:
  flag := 0bv32;
  call {:smack.check_id "ov.bv32"} __SMACK_check_overflow(flag);
  return;
}
