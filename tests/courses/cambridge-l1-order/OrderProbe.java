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

    private static void objectCheck(String name, Location cell, Expression expr)
            throws CanNotReduce {
        State store = new State().add(cell, new Int(0));
        StringJoiner history = new StringJoiner(",");
        int fuel = 8;
        while (true) {
            history.add(store.lookup(cell).toString());
            if (expr instanceof Value) {
                String result = expr instanceof Skip ? "skip" : expr.toString();
                if (expr instanceof Bool) {
                    result = Boolean.toString(((Bool) expr).value);
                }
                report("l1", name, result, history);
                return;
            }
            if (fuel-- == 0) {
                throw new AssertionError("L1 step budget exhausted");
            }
            expr = expr.smallStep(store);
        }
    }

    private static Expression write(Location cell, int n) {
        return new Assign(cell, new Int(n));
    }

    private static Expression operand(Location cell, int n) {
        return new Seq(write(cell, n), new Int(0));
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
    }
}
