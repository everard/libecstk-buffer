# DESCRIPTION
Essential Component Stack - libecstk - is a small modular C++20 library. Buffer module features type-safe buffers which are similar to std::array, but with some
type-safe compile-time-checked slice/join/view operations.

# INSTALLATION
Note: _Buffer module is header-only._

Development headers can be copied to the `/usr/local/include/ecstk` directory using the following command.

```
sudo make install
```

The installed development headers can be removed using the following command.

```
sudo make uninstall
```

There's a number of tests for this module. To compile them, run:

```
mkdir build
make
```

Note: A C++20-capable compiler is required.

# USAGE
## BUFFER
*All types from this section are located in the `ecstk` namespace.*

In this library a _buffer_ is a type which contains (or references) an array of the given value type and size.

A _buffer_ also has a _tag type_. This _tag type_ helps to differentiate between buffers of the same value type and size (see the [BUFFER TAG TYPES](#buffer-tag-types)
section for details).

There are 3 kinds of buffers:

 * `buffer`, `secure_buf` - aggregates, the last one zeroes out the memory it holds upon its destruction;
 * `buffer_ref` - not an aggregate, can only be constructed from the other two buffer types, behaves as a reference to existing buffer objects.

### BUFFER CONCEPTS
This module defines the following concepts:

* `static_buffer` - matches any kind of buffer type;
* `static_byte_buffer` - matches any kind of buffer type whose value type is `unsigned char`;
* `byte_range` - any `std::ranges::sized_range` whose value type is `unsigned char`.

There are also the following type aliases:

* `mut_byte_sequence` for `std::span<unsigned char>`;
* `byte_sequence` for `std::span<unsigned char const>`.

### BUFFER REFERENCES, BUFFER VIEWING
Buffer reference type, `buffer_ref`, behaves exactly as a normal C++ reference, i.e. it has the same interface as the corresponding `buffer` or `secure_buf`.
Its purpose is to avoid construction of temporary buffers. The `buffer_ref` type contains only a single pointer, so it has zero overhead over a normal C++ reference.
In practice, the `buffer_ref` type should _almost never be used directly_. The `ref`/`mut_ref` templates should be used instead.

Note: All function templates which create `buffer_ref`s are _always_ safe to use. Possible buffer overflow is checked at compile time.

Now, how can this reference type benefit your code? Let's consider the following example.

Let's say we have a 256-byte packet which we know starts with two 32-byte frames. We want to parse this packet and process these two starting frames.

The following code shows how this can be done using this library's type-safe buffer interface.

```
#include <ecstk/buffer.hh>

using ecstk::buffer;
using ecstk::ref;

// Note: ecstk::ref<T> behaves similarly to T const&.
// Note: ecstk::mut_ref<T> behaves similarly to T&.

using packet = buffer<256>;
using frame = buffer<32>;

void
process_frame(ref<frame> f) {
    // Do something with {f}.
}

void
parse(ref<packet> pkt) {
    auto [f0, f1] = pkt.template view_as<frame, frame>();
    process_frame(f0);
    process_frame(f1);
}
```

If normal C++ reference was used as the parameter for the `process_frame` function, then construction of temporary objects would be necessary. But in this example we
essentially just take two pointers.

This example uses variadic `view_as` member function template which, depending on the number of its template parameters,
returns either an object of type `buffer_ref`, or a `std::tuple` of `buffer_ref`s. This member function template can also make buffer references
starting from some offset:

```
// This makes buffer_refs starting from pkt's 16-th byte.
auto [f0, f1] = pkt.template view_as<16, frame, frame>();
```

All offset computations are performed at compile time, and buffer overflow can never happen: if, for instance, the packet's size was 63 instead of 256,
then C++ compiler would detect buffer overflow and the code would not compile.

There's another useful variadic function template which can create `buffer_ref`s: `view_buffer_by_chunks`. It is a non-member function template which
takes one buffer as an input, let's call it `x`, and creates an array of `buffer_ref`s of the specified size which reference successive parts of `x`
(these `buffer_ref`s all have the same value and tag types as the initial buffer).
Let's take a look at the following example.

```
// pkt is of type packet from example above.
auto chunks = view_buffer_by_chunks<32>(pkt);
```

Here `chunks` is an 8-element (256 / 32 = 8) `buffer` of `buffer_ref`s each having their size equal to 32.
The `view_buffer_by_chunks` template function always checks that division does not produce a remainder: in the example above it
checks at compile time if (256 % 32 == 0).

### BUFFER JOINING
Buffers can be joined (concatenated) using the `join_buffers` and `join_buffers_secure` non-member variadic function templates:

```
// In the following x0, x1, x2 are buffers or buffer_refs.
auto buf0 = join_buffers(x0, x1, x2);
auto buf1 = join_buffers_secure(x0, x1, x2);

// Note: buf0 is buffer, buf1 is secure_buf.
// Note: buf0 has the same contents as buf1, i.e. concatenation of x0, x1 and x2.
```

### BUFFER COPYING/FILLING/EXTRACTION
Note: All function templates which copy/fill/extract buffers are _always_ safe to use. Possible buffer overflow is checked at compile time.
Copy/fill operations are also safe for overlapping buffers (this situation may happen when `buffer_ref`s are used), since these operations
use `std::copy_n` algorithm which doesn't require non-overlapping ranges (unlike `std::copy` which _requires_ non-overlapping source and destination ranges).

Contents of one buffer, let's call it `src`, can be copied to a non-empty list of buffers
using the `copy_into` variadic member function template:

```
// Copy elements from src successively into x0, x1, x2:
src.copy_into(x0, x1, x2);

// Copy elements from src, starting from offset 21 (in src), successively into x0, x1, x2:
src.copy_into<21>(x0, x1, x2);
```

Contents of one buffer, let's call it `dst`, can be filled from a non-empty list of buffers
using the `fill_from` variadic member function template:

```
// Copy elements from x0, x1, x2 successively into dst:
dst.fill_from(x0, x1, x2);

// Copy elements from x0, x1, x2 successively into dst, starting from offset 21 (in dst):
dst.fill_from<21>(x0, x1, x2);
```

Contents of one buffer, let's call it `src`, can be extracted to another buffer, or a `std::tuple` of buffers,
using the `extract` variadic member function template:

```
using ecstk::buffer;
using buf0 = buffer<21>;
using buf1 = buffer<12>;
using buf2 = buffer<42>;

// Extract elements from src to b0 which has type buf0:
auto b0 = src.extract<buf0>();

// Extract elements from src to std::tuple<buf0, buf1, buf2>:
auto [b1, b2, b3] = src.extract<buf0, buf1, buf2>();

// Extract elements from src to b4 of type buf0, starting from offset 21:
auto b4 = src.extract<21, buf0>();

// Extract elements from src to std::tuple<buf0, buf1, buf2>, starting from offset 21:
auto [b5, b6, b7] = src.extract<21, buf0, buf1, buf2>();
```

### BUFFER TO INTEGER CONVERSION
Any integer of type `T` can be converted to and from a buffer whose value type is `unsigned char` and size equals to `sizeof(T)` using
the `int_to_buffer` and `buffer_to_int` non-member function templates:

```
using buf = ecstk::buffer<sizeof(unsigned)>;

unsigned i = 57;
auto b0 = ecstk::int_to_buffer(i);

auto b1 = buf{};
int_to_buffer(i, b1); // ADL should find this function template in ecstk namespace.

// Postcondition: b0 == b1

auto j = buffer_to_int<unsigned>(b0); // ADL should also be able to find this function template.
auto k = unsigned{};
buffer_to_int(b1, k);

// Postcondition: (i == j) && (j == k)
```

### BUFFER TAG TYPES
Here's an example from cryptography of when _tag types_ can be useful. Let's say we have two key types: one for stream cipher and another one for MAC (message authentication code).
Both are buffers of `unsigned char`s of size 32:

```
using ecstk::secure_buf;

using cipher_key = secure_buf<32, unsigned char>;
using mac_key = secure_buf<32, unsigned char>;
```

But this two types are in realty one type, i.e. `secure_buf<32, unsigned char>`, and using one key in place of the other is totally fine from compiler's point of view, while
actually doing so is logical error.

Tag types for the rescue:

```
struct cipher_key_tag {};
struct mac_key_tag {};

using cipher_key = secure_buf<32, unsigned char, cipher_key_tag>;
using mac_key = secure_buf<32, unsigned char, mac_key_tag>;
```

Now, `cipher_key` and `mac_key` are different types, and compiler will catch the misuse of one key when the other one is required.

Note that `buffer_ref` also contains tag type, so using `ref` in function parameters guarantees type safety:

```
void
encrypt(ref<cipher_key> k);

void
compute_mac(ref<mac_key> k);
```

# LICENSE
Copyright Nezametdinov E. Ildus 2021.

Distributed under the Boost Software License, Version 1.0.
(See accompanying file LICENSE_1_0.txt or copy at https://www.boost.org/LICENSE_1_0.txt)
