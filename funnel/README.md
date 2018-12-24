# Spec

Assumed log is like this:

```
timestamp: (Field1, Value1), (Field2, Value2) ... (FiledN, ValueN)
```

Assign `u64` to each logs, then all logs have a unique number.

```text
timestamp1: ID(1): (Field1, Value1), (Field2, Value2) ... (FieldN, ValueN)
timestamp2: ID(2): (Field2, Value2), (Field3, Value3) ... (FieldN, ValueN)
timestamp3: ID(3): (Field3, Value3), (Field4, Value4) ... (FieldN, ValueN)
```

1) Build `Radix Tree` from timestamp and `ID`.

2) Build `Bloom Filter` from pairs `(Field, Value)`.

```text
ID(1): 0b_1001010100101010101.....
ID(2): 0b_1000010100010101111.....
ID(3): 0b_0001111111001010100.....
```

## License

Licensed under either of

 * Apache License, Version 2.0
   ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license
   ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.
