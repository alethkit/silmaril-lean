/* C => C translations of add3 (examples/compiles-to/straight/straight.c), one per function.
   add3_reassoc is a correct reassociation; the others carry a deliberate bug. */
int add3_reassoc(int a, int b, int c)
{
  int s = b + c;
  int t = a + s;
  return t;
}

int add3_op(int a, int b, int c)
{
  int s = a + b;
  int t = s - c;
  return t;
}

int add3_double(int a, int b, int c)
{
  int s = a + b;
  int t = s + c;
  int u = t + t;
  return u;
}

int add3_operand(int a, int b, int c)
{
  int s = a + b;
  int t = s + a;
  return t;
}

int add3_drop(int a, int b, int c)
{
  int s = a + b;
  return s;
}
