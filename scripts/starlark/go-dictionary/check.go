// Run from the pinned starlark-go checkout.
package main

import (
	"fmt"
	"math"
	"math/big"
	"slices"
	"strings"

	"go.starlark.net/starlark"
	"go.starlark.net/syntax"
)

func require(ok bool, message string) {
	if !ok {
		panic(message)
	}
}

func fromBits(bits uint64) starlark.Float { return starlark.Float(math.Float64frombits(bits)) }

func wrap(key starlark.Value) starlark.Value {
	for range 10 {
		key = starlark.Tuple{key}
	}
	return key
}

func checkHashes() {
	large := new(big.Int).Lsh(big.NewInt(1), 80)
	large.Neg(large.Add(large, big.NewInt(1)))
	for _, tc := range []struct {
		key  starlark.Value
		want uint32
	}{
		{starlark.None, 0x00000000}, {starlark.False, 0x00000000}, {starlark.True, 0x00000001},
		{starlark.MakeInt(-3), 0x00000000},
		{starlark.MakeInt64(-2147483649), 0x83000014}, {starlark.MakeInt64(-2147483648), 0x8240000f},
		{starlark.MakeInt64(2147483647), 0x8180000a}, {starlark.MakeInt64(2147483648), 0x8240000f},
		{starlark.MakeInt(0), 0x0240000f}, {starlark.MakeInt64(1 << 32), 0x0240000f},
		{starlark.MakeBigInt(large), 0x03000014},
		{fromBits(0x8000000000000000), 0x0240000f}, {fromBits(0x3ff8000000000000), 0x03000014},
		{fromBits(0xc00e000000000000), 0x00000000}, {fromBits(1), 0x0240000f},
		{fromBits(0x43e0000000000001), 0x0240280f}, {fromBits(0xc3e0000000000001), 0x0240280f},
		{fromBits(0x7ff0000000000000), 0x0018b071}, {fromBits(0xfff0000000000000), 0x0018b071},
		{fromBits(0x7ff8000000000021), 0x0018b071}, {fromBits(0xfff0000000000001), 0x0018b071},
		{starlark.Tuple{}, 0x00345678},
		{starlark.Tuple{starlark.False, starlark.MakeInt(3), fromBits(0xc00e000000000000),
			starlark.Tuple{starlark.MakeInt64(1 << 32), fromBits(0x7ff8000000000021)}}, 0x8ebb258c},
		{wrap(starlark.MakeInt(0)), 0xa77087e7}, {wrap(starlark.MakeInt64(1 << 32)), 0xa77087e7},
	} {
		hash, err := tc.key.Hash()
		require(err == nil && hash == tc.want, fmt.Sprintf("%v: hash %08x, want %08x (%v)", tc.key, hash, tc.want, err))
	}
	fmt.Println("PASS pinned scalar and tuple hash vectors")
}

// This host-only diagnostic records actual probe order in the pinned table.
type traceKey struct {
	id        int
	word      uint32
	visits    *[]int
	hashCalls *int
}

func (k traceKey) String() string     { return fmt.Sprint(k.id) }
func (traceKey) Type() string         { return "trace_key" }
func (traceKey) Freeze()              {}
func (traceKey) Truth() starlark.Bool { return starlark.True }
func (k traceKey) Hash() (uint32, error) {
	if k.hashCalls != nil {
		*k.hashCalls++
	}
	return k.word, nil
}
func (k traceKey) CompareSameType(op syntax.Token, y starlark.Value, depth int) (bool, error) {
	require(op == syntax.EQL && depth == starlark.CompareLimit, "unexpected key comparison")
	other := y.(traceKey)
	if k.visits != nil {
		*k.visits = append(*k.visits, other.id)
	}
	return k.id == other.id, nil
}

func checkSlots() {
	traced := starlark.NewDict(0)
	for i := range 8 {
		require(traced.SetKey(traceKey{id: i, word: 1}, starlark.MakeInt(i)) == nil, "trace insertion failed")
	}
	var visited []int
	_, found, err := traced.Get(traceKey{id: 3, word: 1, visits: &visited})
	require(err == nil && found && slices.Equal(visited, []int{7, 6, 5, 4, 3}),
		fmt.Sprintf("unexpected slot prefix %v (%v)", visited, err))
	require(traced.SetKey(traceKey{id: 3, word: 1}, starlark.MakeInt(99)) == nil, "trace replacement failed")
	visited = nil
	_, found, err = traced.Get(traceKey{id: -1, word: 1, visits: &visited})
	require(err == nil && !found && slices.Equal(visited, []int{7, 6, 5, 4, 3, 2, 1, 0}),
		fmt.Sprintf("unexpected slot order after replacement %v (%v)", visited, err))

	dict := starlark.NewDict(0)
	for i := range 8 {
		key := starlark.MakeInt64(int64(i) << 32)
		require(dict.SetKey(key, starlark.MakeInt(i)) == nil, "numeric collision insertion failed")
	}
	require(dict.SetKey(fromBits(0x8000000000000000), starlark.MakeInt(99)) == nil, "float alias replacement failed")
	for i, key := range dict.Keys() {
		integer, ok := key.(starlark.Int)
		require(ok, "replacement changed the stored key type")
		bits, fits := integer.Int64()
		require(fits && bits == int64(i)<<32, "replacement changed numeric key or iteration order")
		want := i
		if i == 0 {
			want = 99
		}
		value, found, err := dict.Get(key)
		require(err == nil && found && value == starlark.MakeInt(want), "wrong colliding key value")
	}
	require(dict.Len() == 8, "replacement at capacity grew the dictionary")
	fmt.Println("PASS single-bucket slot order, eight numeric collisions, and in-place replacement")
}

func checkGrowth() {
	traced := starlark.NewDict(0)
	var hashCalls int
	for i := range 13 {
		if i == 8 || i == 12 {
			// A hit at eight must skip the first rehash. Another hit exercises overflow.
			before := hashCalls
			replaced := 3
			if i == 12 {
				replaced = 8
			}
			require(traced.SetKey(traceKey{id: replaced, word: 1}, starlark.MakeInt(99)) == nil,
				"growth fixture replacement failed")
			require(hashCalls == before, "replacement rehashed stored keys")
		}
		require(traced.SetKey(traceKey{id: i, word: 1, hashCalls: &hashCalls}, starlark.MakeInt(i)) == nil,
			"growth fixture insertion failed")
		if i == 8 {
			require(hashCalls == 17, "ninth miss must recompute all eight stored hashes")
		}
	}
	for i, key := range traced.Keys() {
		saved := key.(traceKey)
		require(saved.id == i && saved.hashCalls == &hashCalls, "rehash or replacement changed a stored key")
	}
	var visited []int
	_, found, err := traced.Get(traceKey{id: -1, word: 1, visits: &visited})
	require(err == nil && !found && slices.Equal(visited, []int{7, 6, 5, 4, 3, 2, 1, 0, 8, 12, 11, 10, 9}),
		fmt.Sprintf("unexpected primary and overflow order %v (%v)", visited, err))

	split := starlark.NewDict(0)
	for i := range 9 {
		word := uint32(1)
		if i == 0 {
			word = 2
		}
		require(split.SetKey(traceKey{id: i, word: word}, starlark.MakeInt(i)) == nil, "split trace insertion failed")
	}
	visited = nil
	_, found, err = split.Get(traceKey{id: -1, word: 1, visits: &visited})
	require(err == nil && !found && slices.Equal(visited, []int{8, 7, 6, 5, 4, 3, 2, 1}),
		fmt.Sprintf("ninth key must fit the split primary chain, visited %v (%v)", visited, err))

	for _, splitBit := range []bool{false, true} {
		dict := starlark.NewDict(0)
		keyAt := func(i int) int64 {
			if splitBit && i == 0 {
				return 1
			}
			return int64(i) << 32
		}
		for i := range 13 {
			if i == 8 {
				aliasBits := uint64(0x8000000000000000)
				if splitBit {
					aliasBits = 0x3ff0000000000000
				}
				require(dict.SetKey(fromBits(aliasBits), starlark.MakeInt(99)) == nil, "numeric alias replacement failed")
			}
			require(dict.SetKey(starlark.MakeInt64(keyAt(i)), starlark.MakeInt(i)) == nil, "post-threshold insertion failed")
		}
		for i, key := range dict.Keys() {
			integer, ok := key.(starlark.Int)
			require(ok, "rehash changed the stored integer to its float alias")
			bits, fits := integer.Int64()
			require(fits && bits == keyAt(i), "rehash changed iteration order or key")
			want := i
			if i == 0 {
				want = 99
			}
			value, found, err := dict.Get(key)
			require(err == nil && found && value == starlark.MakeInt(want), "rehash lost a numeric key or value")
		}
		require(dict.Len() == 13, "unexpected numeric count after growth")
	}
	fmt.Println("PASS first rehash, full-hash collisions, low-bit split, overflow slots and stored keys")
}

func checkDepthError() {
	zero, one := starlark.MakeInt(0), starlark.MakeInt(1)
	deep, colliding := wrap(zero), wrap(starlark.MakeInt64(1<<32))
	dict := starlark.NewDict(0)
	require(dict.SetKey(colliding, one) == nil, "deep key insertion failed")
	_, found, err := dict.Get(deep)
	require(!found && err != nil && strings.Contains(err.Error(), "maximum recursion depth"),
		fmt.Sprintf("want a reached depth error for an unequal colliding key, got %v", err))
	require(dict.SetKey(deep, one) != nil && dict.Len() == 1, "failed probe changed the dictionary")
	member, err := starlark.Binary(syntax.IN, deep, dict)
	require(err == nil && member == starlark.False, "mapping membership did not project the lookup error to a miss")

	cycle := starlark.NewDict(0)
	require(cycle.SetKey(zero, cycle) == nil, "cycle construction failed")
	left, right := starlark.NewDict(0), starlark.NewDict(0)
	require(left.SetKey(deep, cycle) == nil && right.SetKey(wrap(fromBits(0x8000000000000000)), cycle) == nil,
		"deep alias insertion failed")
	equal, err := starlark.Compare(syntax.EQL, left, right)
	require(err == nil && !equal, fmt.Sprintf("lookup error should mask the cyclic value, got %v (%v)", equal, err))
	_, err = starlark.Compare(syntax.EQL, cycle, cycle)
	require(err != nil && strings.Contains(err.Error(), "maximum recursion depth"), "cyclic value should fail when reached")
	fmt.Println("PASS raw deep collision errors, membership projection, and cyclic-value masking")
}

func checkGrownDepthError() {
	deep, alias := wrap(starlark.MakeInt(0)), wrap(fromBits(0x8000000000000000))
	cycle := starlark.NewDict(0)
	require(cycle.SetKey(starlark.MakeInt(0), cycle) == nil, "growth cycle construction failed")

	left, right := starlark.NewDict(0), starlark.NewDict(0)
	require(left.SetKey(deep, cycle) == nil && right.SetKey(alias, cycle) == nil, "growth deep key insertion failed")
	for i := range 8 {
		if i == 7 {
			err := right.SetKey(deep, cycle)
			require(err != nil && strings.Contains(err.Error(), "maximum recursion depth") && right.Len() == 8,
				"key depth error must precede growth at eight")
		}
		key := starlark.MakeInt(i)
		require(left.SetKey(key, cycle) == nil && right.SetKey(key, cycle) == nil, "growth filler insertion failed")
	}
	_, found, err := right.Get(deep)
	require(!found && err != nil && strings.Contains(err.Error(), "maximum recursion depth"),
		"grown table lost raw lookup error")
	member, err := starlark.Binary(syntax.IN, deep, right)
	require(err == nil && member == starlark.False, "grown table did not mask membership lookup error")
	equal, err := starlark.Compare(syntax.EQL, left, right)
	require(err == nil && !equal, "grown table did not mask the cyclic value")
	fmt.Println("PASS threshold error precedes growth and grown lookup masks a cyclic value")
}

func main() {
	require(starlark.CompareLimit == 10, "pinned default comparison limit changed")
	checkHashes()
	checkSlots()
	checkGrowth()
	checkDepthError()
	checkGrownDepthError()
}
