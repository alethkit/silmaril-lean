// Run from the pinned starlark-go checkout.
package main

import (
	"fmt"
	"math"
	"math/big"
	"strings"

	"go.starlark.net/starlark"
	"go.starlark.net/syntax"
)

func require(ok bool, message string) {
	if !ok {
		panic(message)
	}
}

func call(name string, input starlark.Value) (starlark.Value, error) {
	return starlark.Call(&starlark.Thread{Name: "binary64"}, starlark.Universe[name], starlark.Tuple{input}, nil)
}

func fromBits(bits uint64) starlark.Float { return starlark.Float(math.Float64frombits(bits)) }

func checkUnary() {
	for _, tc := range []struct {
		name      string
		bits, abs uint64
		truth     starlark.Bool
	}{
		{"positive zero", 0, 0, false},
		{"negative zero", 0x8000000000000000, 0, false},
		{"negative subnormal", 0x8000000000000001, 1, true},
		{"negative finite", 0xbff4000000000000, 0x3ff4000000000000, true},
		{"negative max finite", 0xffefffffffffffff, 0x7fefffffffffffff, true},
		{"positive infinity", 0x7ff0000000000000, 0x7ff0000000000000, true},
		{"negative infinity", 0xfff0000000000000, 0x7ff0000000000000, true},
		{"positive quiet NaN", 0x7ff8000000000021, 0x7ff8000000000021, true},
		{"negative signaling NaN", 0xfff0000000000001, 0x7ff0000000000001, true},
	} {
		x := fromBits(tc.bits)
		result, err := call("abs", x)
		abs, ok := result.(starlark.Float)
		require(err == nil && ok && math.Float64bits(float64(abs)) == tc.abs,
			fmt.Sprintf("%s: want abs bits %x, got %x (%v)", tc.name, tc.abs, math.Float64bits(float64(abs)), err))
		truth, err := call("bool", x)
		require(err == nil && truth == tc.truth, fmt.Sprintf("%s: truth %v (%v)", tc.name, truth, err))
		tag, err := call("type", x)
		require(err == nil && tag == starlark.String("float"), fmt.Sprintf("%s: type %v (%v)", tc.name, tag, err))
	}
	fmt.Println("PASS raw binary64 abs, truth and type, including signed zeros, infinities and NaN payloads")
}

func checkEqualityAndKeys() {
	for _, pair := range [][2]starlark.Value{
		{fromBits(0x8000000000000000), fromBits(0)},
		{fromBits(0xfff8000000000021), fromBits(0x7ff0000000000001)},
		{starlark.Float(1.0), starlark.MakeInt(1)},
	} {
		x, y := pair[0], pair[1]
		equal, err := starlark.Equal(x, y)
		require(err == nil && equal, fmt.Sprintf("%v == %v failed (%v)", x, y, err))
		hx, ex := x.Hash()
		hy, ey := y.Hash()
		require(ex == nil && ey == nil && hx == hy, fmt.Sprintf("inconsistent hash for %v, %v", x, y))

		for _, keys := range [][2]starlark.Value{{x, y}, {starlark.Tuple{x}, starlark.Tuple{y}}} {
			d := starlark.NewDict(1)
			require(d.SetKey(keys[0], starlark.True) == nil, "Go did not accept a float key")
			v, found, err := d.Get(keys[1])
			require(err == nil && found && v == starlark.True, fmt.Sprintf("no matching key for %v", keys[1]))
		}
	}
	greater, err := starlark.Compare(syntax.GT, fromBits(0x7ff8000000000001), starlark.Float(math.Inf(1)))
	require(err == nil && greater, "Go did not order NaN above infinity")
	equal, err := starlark.Equal(starlark.Float(1<<53), starlark.MakeInt64((1<<53)+1))
	require(err == nil && !equal, "Go rounded an integer in mixed comparison")
	fmt.Println("PASS Go equality and hash controls for signed zeros, NaNs, mixed numbers and tuple keys")
}

func checkConversionOverflow() {
	huge := starlark.MakeBigInt(new(big.Int).Lsh(big.NewInt(1), 1100))
	for _, input := range []starlark.Value{huge, starlark.String("1e9999")} {
		_, err := call("float", input)
		require(err != nil && strings.Contains(err.Error(), "too large"), fmt.Sprintf("want conversion overflow, got %v", err))
	}
	value, err := call("float", starlark.String("-inf"))
	require(err == nil && value == starlark.Float(math.Inf(-1)), fmt.Sprintf("explicit infinity %v (%v)", value, err))
	product, err := starlark.Binary(syntax.STAR, starlark.Float(math.MaxFloat64), starlark.Float(2))
	require(err == nil && product == starlark.Float(math.Inf(1)), fmt.Sprintf("arithmetic overflow %v (%v)", product, err))
	fmt.Println("PASS Go rejects conversion overflow and admits explicit or arithmetic infinity")
}

func main() {
	checkUnary()
	checkEqualityAndKeys()
	checkConversionOverflow()
}
