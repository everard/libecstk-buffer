// Copyright(c) 2021 Nezametdinov E. Ildus.
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// https://www.boost.org/LICENSE_1_0.txt)
//
#include "../src/buffer.hh"

#include <iostream>
#include <iomanip>
#include <ranges>

#include <deque>
#include <vector>

////////////////////////////////////////////////////////////////////////////////
// Utility functions.
////////////////////////////////////////////////////////////////////////////////

template <ecstk::static_byte_buffer Buffer>
void
print(Buffer const& b) {
    static constexpr int line_width = 80;
    static constexpr int n_numbers_per_line = line_width / 2;

    for(std::size_t i{}, j{}; auto x : b) {
        std::cout << std::setfill('0') << std::setw(2) << std::hex << (int)x;

        if(++j; (++i == n_numbers_per_line) && (j != b.size())) {
            i = 0;
            std::cout << '\n';
        }
    }

    std::cout << std::dec << '\n';
}

template <std::ranges::sized_range Range0, std::ranges::sized_range Range1>
auto
equal(Range0 const& x, Range1 const& y) {
    if constexpr(!std::same_as<std::ranges::range_value_t<Range0>,
                               std::ranges::range_value_t<Range1>>) {
        return false;
    }

    if(std::size(x) != std::size(y)) {
        return false;
    }

    return std::ranges::equal(x, y);
}

void
validate(bool v) {
    std::cout << "[valid result: " << int{v} << "]\n";

    if(!v) {
        std::exit(EXIT_FAILURE);
    }
}

////////////////////////////////////////////////////////////////////////////////
// Compile-time tests.
////////////////////////////////////////////////////////////////////////////////

// Tag.
enum struct simple_tag {};

namespace compile_time_tests {
namespace ecstk = ::ecstk;
namespace std = ::std;

using ecstk::buffer;
using ecstk::secure_buf;
using ecstk::static_sum;

using ecstk::mut_ref;
using ecstk::ref;

template <typename T>
struct alpha {
    static constexpr auto x = 0;
};

template <ecstk::static_buffer T>
struct alpha<T> {
    static constexpr auto x = 1;
};

template <ecstk::static_byte_buffer T>
struct alpha<T> {
    static constexpr auto x = 2;
};

template <std::ranges::sized_range T>
struct alpha<T> {
    static constexpr auto x = 3;
};

template <ecstk::byte_range T>
struct alpha<T> {
    static constexpr auto x = 4;
};

static_assert(alpha<bool>::x == 0);
static_assert(alpha<unsigned>::x == 0);
static_assert(alpha<simple_tag>::x == 0);

static_assert(alpha<buffer<5, unsigned>>::x == 1);
static_assert(alpha<ref<buffer<5, unsigned>>>::x == 1);
static_assert(alpha<mut_ref<buffer<5, unsigned>>>::x == 1);

static_assert(alpha<secure_buf<5, unsigned>>::x == 1);
static_assert(alpha<ref<secure_buf<5, unsigned>>>::x == 1);
static_assert(alpha<mut_ref<secure_buf<5, unsigned>>>::x == 1);

static_assert(alpha<buffer<5>>::x == 2);
static_assert(alpha<ref<buffer<5>>>::x == 2);
static_assert(alpha<mut_ref<buffer<5>>>::x == 2);

static_assert(alpha<secure_buf<5>>::x == 2);
static_assert(alpha<ref<secure_buf<5>>>::x == 2);
static_assert(alpha<mut_ref<secure_buf<5>>>::x == 2);

static_assert(alpha<std::array<unsigned, 5>>::x == 3);
static_assert(alpha<std::array<char, 5>>::x == 3);
static_assert(alpha<std::deque<unsigned>>::x == 3);
static_assert(alpha<std::vector<unsigned>>::x == 3);

static_assert(alpha<std::array<unsigned char, 5>>::x == 4);
static_assert(alpha<std::deque<unsigned char>>::x == 4);
static_assert(alpha<std::vector<unsigned char>>::x == 4);
static_assert(alpha<ecstk::byte_sequence>::x == 4);
static_assert(alpha<ecstk::mut_byte_sequence>::x == 4);

static_assert(static_sum<5, 10, 334, 3485, 223> == 4057);

static_assert(ecstk::static_buffer<buffer<20, unsigned char, simple_tag>>);
static_assert(ecstk::static_buffer<secure_buf<20, unsigned char, simple_tag>>);
static_assert(ecstk::static_buffer<ref<buffer<20, unsigned char, simple_tag>>>);
static_assert(
    ecstk::static_buffer<ref<secure_buf<20, unsigned char, simple_tag>>>);
static_assert(
    ecstk::static_byte_buffer<ref<buffer<20, unsigned char, simple_tag>>>);
static_assert(
    ecstk::static_byte_buffer<ref<secure_buf<20, unsigned char, simple_tag>>>);
static_assert(
    !ecstk::static_byte_buffer<ref<buffer<20, unsigned, simple_tag>>>);
static_assert(
    !ecstk::static_byte_buffer<ref<secure_buf<20, unsigned, simple_tag>>>);
static_assert(std::same_as<
              unsigned char const,
              typename ref<buffer<20, unsigned char, simple_tag>>::value_type>);
static_assert(!std::same_as<
              unsigned char,
              typename ref<buffer<20, unsigned char, simple_tag>>::value_type>);
static_assert(!ecstk::static_buffer<std::array<unsigned char, 20>>);
static_assert(ecstk::byte_range<std::array<unsigned char, 20>>);

static_assert(ecstk::are_homogeneous_buffers<
              buffer<5>, buffer<20, unsigned char, simple_tag>, buffer<25>>);
static_assert(ecstk::are_homogeneous_buffers<
              buffer<5, unsigned char const>,
              buffer<20, unsigned char, simple_tag>, buffer<25>>);
static_assert(
    !ecstk::are_homogeneous_buffers<
        buffer<5, char>, buffer<20, unsigned char, simple_tag>, buffer<25>>);
static_assert(!ecstk::are_homogeneous_buffers<
              buffer<5, char>, buffer<20, int, simple_tag>, buffer<25, char>>);
static_assert(
    !ecstk::are_homogeneous_buffers<
        buffer<5, char>, buffer<20, char, simple_tag>, buffer<25, unsigned>>);

static_assert(
    ecstk::is_valid_buffer_conversion<
        long, buffer<ecstk::integer_size<long>, unsigned char, simple_tag>>);
static_assert(ecstk::is_valid_buffer_conversion<
              long, secure_buf<ecstk::integer_size<long>>>);
static_assert(
    !ecstk::is_valid_buffer_conversion<
        long,
        buffer<ecstk::integer_size<long> + 1, unsigned char, simple_tag>>);

// These are hard errors:
// static_assert(!ecstk::is_valid_buffer_conversion<
//              long, std::array<unsigned char, ecstk::integer_size<long>>>);
// static_assert(!ecstk::is_valid_buffer_conversion<bool, buffer<1>>);

// clang-format off
template <typename Buffer0, typename Buffer1>
concept referenceable =
    requires(Buffer0 x0) {
        { ref<Buffer1>{x0} };
    };

template <typename Buffer_dst, typename Buffer_src0, typename... Buffers_src>
concept fillable_from =
    requires(Buffer_dst dst, Buffer_src0 const src0,
             Buffers_src const... srcs) {
        { dst.fill_from(src0, srcs...) };
    };

template <typename Buffer_src, typename Buffer_dst0, typename... Buffers_dst>
concept extractable_to =
    requires(Buffer_src const src) {
        { src.template extract<Buffer_dst0, Buffers_dst...>() } ->
            std::same_as<
                std::conditional_t<(sizeof...(Buffers_dst) == 0), Buffer_dst0,
                                   std::tuple<Buffer_dst0, Buffers_dst...>>>;
    };
// clang-format on

static_assert(referenceable<buffer<10>, buffer<10>>);
static_assert(referenceable<buffer<10, int>, buffer<10, int>>);
static_assert(
    referenceable<buffer<10, int, simple_tag>, buffer<10, int, simple_tag>>);
static_assert(
    !referenceable<buffer<10, unsigned>, buffer<10, unsigned, simple_tag>>);
static_assert(
    !referenceable<buffer<10, unsigned, simple_tag>, buffer<10, unsigned>>);
static_assert(!referenceable<buffer<10, unsigned>, buffer<10, int>>);
static_assert(!referenceable<buffer<10>, buffer<11>>);

static_assert(fillable_from<buffer<10>, buffer<9>>);
static_assert(fillable_from<buffer<10>, buffer<10>>);
static_assert(fillable_from<buffer<10>, buffer<4>, buffer<3>>);
static_assert(fillable_from<buffer<10>, buffer<4>, buffer<6>>);
static_assert(fillable_from<buffer<10>, buffer<2>, buffer<3>, buffer<5>>);
static_assert(!fillable_from<buffer<10>, buffer<11>>);
static_assert(!fillable_from<buffer<10>, buffer<20>>);
static_assert(!fillable_from<buffer<10>, buffer<7>, buffer<4>>);
static_assert(!fillable_from<buffer<10>, buffer<3>, buffer<5>, buffer<3>>);
static_assert(!fillable_from<buffer<10>, buffer<5, int>>);

static_assert(extractable_to<buffer<10>, buffer<10>>);
static_assert(
    extractable_to<buffer<10>, buffer<10, unsigned char, simple_tag>>);
static_assert(extractable_to<buffer<10>, buffer<9>, buffer<1>>);
static_assert(extractable_to<buffer<10>, secure_buf<9>, buffer<1>>);
static_assert(extractable_to<buffer<10>, buffer<3>, buffer<5>, buffer<2>>);
static_assert(extractable_to<buffer<10>, buffer<3>, secure_buf<5>, buffer<2>>);
static_assert(!extractable_to<buffer<10>, buffer<10, int>>);
static_assert(!extractable_to<buffer<10, int>, buffer<10>>);
static_assert(!extractable_to<buffer<10>, ref<buffer<10>>>);
static_assert(!extractable_to<buffer<10>, mut_ref<buffer<10>>>);
static_assert(!extractable_to<buffer<10>, buffer<9>, buffer<2>>);
static_assert(!extractable_to<buffer<10>, buffer<3>, buffer<5>, buffer<3>>);
} // namespace compile_time_tests

////////////////////////////////////////////////////////////////////////////////
// Runtime tests.
////////////////////////////////////////////////////////////////////////////////

int
main() {
    using ecstk::buffer;
    using ecstk::ref;
    using ecstk::secure_buf;

    std::cout << "============================================================="
                 "===================\n"
              << "Buffer fill operations\n"
              << "============================================================="
                 "===================\n";

    std::cout << "-------------------------------------------------------------"
                 "-------------------\n"
              << "without offset\n"
              << "-------------------------------------------------------------"
                 "-------------------\n";

    if(true) {
        auto x = buffer<10>{};
        auto a = buffer<6>{1, 2, 3, 4, 5, 6};
        auto b = buffer<3>{7, 8, 9};
        auto c = buffer<1>{10};
        auto d = buffer<0>{};

        auto expected_x0 = buffer<10>{0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
        auto expected_x1 = buffer<10>{1, 2, 3, 4, 5, 6, 7, 8, 9, 10};

        std::cout << "a: ";
        print(a);
        std::cout << "b: ";
        print(b);
        std::cout << "c: ";
        print(c);
        std::cout << "d: ";
        print(d);
        std::cout << "x0: ";
        print(x);
        validate(equal(x, expected_x0));

        x.fill_from(d, a, d, b, c, d);

        std::cout << "x1: ";
        print(x);
        validate(equal(x, expected_x1));

        auto x2 = secure_buf<10>{};
        x2.fill_from(d, a, d, b, c, d);
        std::cout << "x2: ";
        print(x2);
        validate(equal(x, x2));
    }

    std::cout << "-------------------------------------------------------------"
                 "-------------------\n"
              << "with offset\n"
              << "-------------------------------------------------------------"
                 "-------------------\n";
    if(true) {
        auto x = buffer<10>{};
        auto a = buffer<4>{1, 2, 3, 4};
        auto b = buffer<3>{7, 8, 9};
        auto c = buffer<1>{10};
        auto d = buffer<0>{};

        auto expected_x0 = buffer<10>{0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
        auto expected_x1 = buffer<10>{0, 0, 1, 2, 3, 4, 7, 8, 9, 10};
        auto expected_x2 = buffer<10>{0, 0, 1, 2, 3, 4, 7, 8, 9, 10};

        std::cout << "a: ";
        print(a);
        std::cout << "b: ";
        print(b);
        std::cout << "c: ";
        print(c);
        std::cout << "d: ";
        print(d);
        std::cout << "x0: ";
        print(x);
        validate(equal(x, expected_x0));

        x.fill_from<2>(a, b, c);

        std::cout << "x1: ";
        print(x);
        validate(equal(x, expected_x1));

        x.fill_from<2>(d, a, d, d, b, c, d, d);

        std::cout << "x2: ";
        print(x);
        validate(equal(x, expected_x2));

        auto x2 = secure_buf<10>{};
        x2.fill_from<2>(d, a, d, d, b, c, d, d);
        print(x2);
        validate(equal(x, x2));
    }

    std::cout << "============================================================="
                 "===================\n"
              << "Buffer references and views\n"
              << "============================================================="
                 "===================\n";

    if(true) {
        using test_buffer = buffer<36, unsigned char, simple_tag>;
        static_assert(
            std::same_as<ref<test_buffer>, typename test_buffer::ref>);

        std::cout
            << "-------------------------------------------------------------"
               "-------------------\n"
            << "references\n"
            << "-------------------------------------------------------------"
               "-------------------\n";

        auto b = test_buffer{43, 67, 33, 32, 13, 22, 233, 56, 33, 12, 155, 33,
                             45, 95, 73, 55, 83, 62, 57,  96, 45, 32, 34,  67,
                             77, 32, 23, 18, 63, 19, 52,  67, 12, 90, 137, 14};
        auto b_ref = ref<test_buffer>{b};

        std::cout << "b:\n";
        print(b);
        std::cout << "b ref:\n";
        print(b_ref);
        validate((b.begin() == b_ref.begin()) && (b.end() == b_ref.end()) &&
                 equal(b, b_ref));

        std::cout
            << "-------------------------------------------------------------"
               "-------------------\n"
            << "views\n"
            << "-------------------------------------------------------------"
               "-------------------\n";

        auto [c, d, e, f, g] = b.view_as<buffer<2>, buffer<14>, buffer<3>,
                                         buffer<17>, buffer<0>>();
        auto expected_c = buffer<2>{43, 67};
        auto expected_d = buffer<14>{
            33, 32, 13, 22, 233, 56, 33, 12, 155, 33, 45, 95, 73, 55};
        auto expected_e = buffer<3>{83, 62, 57};
        auto expected_f = buffer<17>{96, 45, 32, 34, 67, 77, 32,  23, 18,
                                     63, 19, 52, 67, 12, 90, 137, 14};
        auto expected_g = buffer<0>{};

        std::cout << "c: ";
        print(c);
        validate(equal(expected_c, c));

        std::cout << "d: ";
        print(d);
        validate(equal(expected_d, d));

        std::cout << "e: ";
        print(e);
        validate(equal(expected_e, e));

        std::cout << "f: ";
        print(f);
        validate(equal(expected_f, f));

        std::cout << "g: ";
        print(g);
        validate(equal(expected_g, g));

        auto chunks = view_buffer_by_chunks<6>(b);
        auto chunks_ref = view_buffer_by_chunks<6>(b_ref);
        buffer<6> expected_chunks[6] = {
            {43, 67, 33, 32, 13, 22}, {233, 56, 33, 12, 155, 33},
            {45, 95, 73, 55, 83, 62}, {57, 96, 45, 32, 34, 67},
            {77, 32, 23, 18, 63, 19}, {52, 67, 12, 90, 137, 14}};

        for(std::size_t i = 0; auto& chunk : chunks) {
            std::cout << "chunk " << i++ << ": ";
            print(chunk);
        }

        auto is_expected_result = (chunks.size() == std::size(expected_chunks));
        if(is_expected_result) {
            for(std::size_t i = 0; i < chunks.size(); ++i) {
                is_expected_result =
                    is_expected_result && equal(chunks[i], expected_chunks[i]);

                is_expected_result =
                    is_expected_result &&
                    (chunks[i].begin() == chunks_ref[i].begin()) &&
                    (chunks[i].end() == chunks_ref[i].end());

                if(!is_expected_result) {
                    break;
                }
            }
        }

        validate(is_expected_result);
    }

    std::cout << "============================================================="
                 "===================\n"
              << "Buffer slice and join operations\n"
              << "============================================================="
                 "===================\n";

    if(true) {
        auto b = buffer<15>{
            'A', 'B', 'C', 'D', 'E', 22, 33, 44, 55, 66, 10, 12, 15, 83, 43};
        auto const& b_ref = b;

        std::cout << "b0: ";
        print(b);

        auto c = b_ref.extract<10, buffer<5>>();
        auto expected_c = buffer<5>{10, 12, 15, 83, 43};
        std::cout << "c: ";
        print(c);
        validate(equal(expected_c, c));

        auto d = b_ref.extract<3, buffer<8>>();
        auto expected_d = buffer<8>{'D', 'E', 22, 33, 44, 55, 66, 10};
        std::cout << "d: ";
        print(d);
        validate(equal(expected_d, d));

        b.fill_from<1>(c);
        auto expected_b = buffer<15>{
            'A', 10, 12, 15, 83, 43, 33, 44, 55, 66, 10, 12, 15, 83, 43};

        std::cout << "b1: ";
        print(b);
        validate(equal(expected_b, b));

        auto [e, f, g] = b_ref.extract<buffer<8>, buffer<2>, buffer<5>>();
        auto expected_e = buffer<8>{'A', 10, 12, 15, 83, 43, 33, 44};
        auto expected_f = buffer<2>{55, 66};
        auto expected_g = buffer<5>{10, 12, 15, 83, 43};

        std::cout << "e: ";
        print(e);
        validate(equal(expected_e, e));

        std::cout << "f: ";
        print(f);
        validate(equal(expected_f, f));

        std::cout << "g: ";
        print(g);
        validate(equal(expected_g, g));

        auto h = buffer<15>{};
        auto expected_h0 =
            buffer<15>{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};

        std::cout << "h0: ";
        print(h);
        validate(equal(expected_h0, h));

        h.fill_from(e, f, g);
        std::cout << "h1: ";
        print(h);
        validate(equal(b, h));

        auto i = join_buffers(e, f, g);
        std::cout << "i: ";
        print(i);
        validate(equal(b, i));

        if(true) {
            auto i1 = join_buffers_secure(e, f, g);
            std::cout << "i1: ";
            print(i1);
            validate(equal(i, i1));
        }

        auto [j, k, l, m, n] = b_ref.extract<buffer<8>, secure_buf<2>,
                                             buffer<0>, buffer<5>, buffer<0>>();
        auto expected_j = buffer<8>{'A', 10, 12, 15, 83, 43, 33, 44};
        auto expected_k = buffer<2>{55, 66};
        auto expected_l = buffer<0>{};
        auto expected_m = buffer<5>{10, 12, 15, 83, 43};
        auto expected_n = buffer<0>{};

        std::cout << "j: ";
        print(j);
        validate(equal(expected_j, j));

        std::cout << "k: ";
        print(k);
        validate(equal(expected_k, k));

        std::cout << "l: ";
        print(l);
        validate(equal(expected_l, l));

        std::cout << "m: ";
        print(m);
        validate(equal(expected_m, m));

        std::cout << "n: ";
        print(n);
        validate(equal(expected_n, n));
    }

    std::cout << "============================================================="
                 "===================\n"
              << "Buffer to integer conversions\n"
              << "============================================================="
                 "===================\n";
    if(true) {
        using ulong = unsigned long;

        auto const x0 = ulong{0xFEACBB23};
        auto x_b0 = ecstk::int_to_buffer(x0);

        std::cout << "x0: " << std::hex << x0 << std::dec << '\n';
        std::cout << "x_b0: ";
        print(x_b0);

        auto x_b1 = buffer<ecstk::integer_size<ulong>>{};
        int_to_buffer(x0, x_b1);

        std::cout << "x_b1: ";
        print(x_b1);
        validate(equal(x_b0, x_b1));

        auto x1 = buffer_to_int<ulong>(x_b1);
        std::cout << "x1: " << std::hex << x1 << std::dec << '\n';
        validate(x0 == x1);
    }

    std::cout << "============================================================="
                 "===================\n"
              << "Success\n"
              << "============================================================="
                 "===================\n";

    return EXIT_SUCCESS;
}
