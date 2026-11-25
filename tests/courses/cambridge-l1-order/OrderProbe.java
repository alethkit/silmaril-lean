import java.util.StringJoiner;

class OrderProbe {
    private final StringJoiner writes = new StringJoiner(",");

    private int mark(int n) {
        writes.add(Integer.toString(n));
        return 0;
    }

    private static void report(String layer, String name, String result, StringJoiner history) {
        System.out.printf("EX11 %s %s %s %s%n", layer, name, result, history);
    }

    private static String objectResult(Location cell, Expression expr, StringJoiner history)
            throws CanNotReduce {
        State store = new State().add(cell, new Int(0));
        int fuel = 8;
        while (true) {
            history.add(store.lookup(cell).toString());
            if (expr instanceof Value) {
                String result = expr instanceof Skip ? "skip" : expr.toString();
                if (expr instanceof Bool) {
                    result = Boolean.toString(((Bool) expr).value);
                }
                return result;
            }
            if (fuel-- == 0) {
                throw new AssertionError("L1 step budget exhausted");
            }
            expr = expr.smallStep(store);
        }
    }

    private static void objectCheck(String name, Location cell, Expression expr)
            throws CanNotReduce {
        StringJoiner history = new StringJoiner(",");
        String result = objectResult(cell, expr, history);
        report("l1", name, result, history);
    }

    private static Expression write(Location cell, int n) {
        return new Assign(cell, new Int(n));
    }

    private static Expression operand(Location cell, int n) {
        return new Seq(write(cell, n), new Int(0));
    }

    private static void reportInteger(String layer, String name, String result) {
        System.out.printf("EX6 %s %s %s%n", layer, name, result);
    }

    private static void checkObjectInteger(String name, Location cell, Expression expr)
            throws CanNotReduce {
        reportInteger("l1", name, objectResult(cell, expr, new StringJoiner(",")));
    }

    private static void integerChecks(Location cell) throws CanNotReduce {
        int max = Integer.MAX_VALUE;
        int min = Integer.MIN_VALUE;
        System.out.printf("EX6 limits %d %d %d%n", Integer.SIZE, min, max);
        reportInteger("host", "upper-wrap", Integer.toString(max + 1));
        reportInteger("host", "lower-wrap", Integer.toString(min + (-1)));
        reportInteger("host", "wrapped-ge-zero", Boolean.toString((max + 1) >= 0));
        reportInteger("host", "zero-ge-wrapped", Boolean.toString(0 >= (max + 1)));

        Expression upper = new Plus(new Int(max), new Int(1));
        Expression lower = new Plus(new Int(min), new Int(-1));
        checkObjectInteger("upper-wrap", cell, upper);
        checkObjectInteger("lower-wrap", cell, lower);
        checkObjectInteger("wrapped-ge-zero", cell, new GTeq(upper, new Int(0)));
        checkObjectInteger("zero-ge-wrapped", cell, new GTeq(new Int(0), upper));
    }

    public static void main(String[] args) throws CanNotReduce {
        Location cell = new Location("l");
        objectCheck("plus", cell, new Plus(operand(cell, 1), operand(cell, 2)));
        objectCheck("ge", cell, new GTeq(operand(cell, 1), operand(cell, 2)));
        objectCheck("seq", cell, new Seq(write(cell, 1), write(cell, 2)));

        OrderProbe plus = new OrderProbe();
        report("host", "plus", Integer.toString(plus.mark(1) + plus.mark(2)), plus.writes);
        OrderProbe ge = new OrderProbe();
        report("host", "ge", Boolean.toString(ge.mark(1) >= ge.mark(2)), ge.writes);
        OrderProbe seq = new OrderProbe();
        seq.mark(1);
        seq.mark(2);
        report("host", "seq", "skip", seq.writes);
        integerChecks(cell);
    }
}
