/* Two pointers added: C11 6.5.6p2 allows pointer + integer, never pointer + pointer. */
int *addp(int *p, int *q)
{
  return p + q;
}
