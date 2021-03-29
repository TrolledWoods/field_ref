# field\_ref
Get efficient references to fields.

*This library is still a work in progress*

```rust
use field_ref::field;

struct Struct(u32, u32);

let a = field!(Struct=>0);
let b = field!(Struct=>1);
assert_ne!(a, b);

let mut s = Struct(1, 2);

a.set(&mut s, 4);
assert_eq!(s.0, 4);
```
