// Copyright Nezametdinov E. Ildus 2021.
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// https://www.boost.org/LICENSE_1_0.txt)
//
#ifndef H_639425CCA60E448B9BEB43186E06CA57
#define H_639425CCA60E448B9BEB43186E06CA57

#include <type_traits>
#include <algorithm>
#include <array>

#include <climits>
#include <cstddef>
#include <cstdint>

#include <limits>
#include <ranges>
#include <span>

#include <concepts>
#include <utility>
#include <tuple>

namespace ecstk {
namespace std = ::std;

////////////////////////////////////////////////////////////////////////////////
// Utility types.
////////////////////////////////////////////////////////////////////////////////

using std::size_t;

////////////////////////////////////////////////////////////////////////////////
// Compile-time addition of values of unsigned type. Generates compilation error
// on wrap-around.
////////////////////////////////////////////////////////////////////////////////

namespace detail {

template <std::unsigned_integral T, T X, T Y, T... Rest>
constexpr auto
static_add() noexcept -> T requires(static_cast<T>(X + Y) >= Y) {
    if constexpr(sizeof...(Rest) == 0) {
        return (X + Y);
    } else {
        return static_add<T, static_cast<T>(X + Y), Rest...>();
    }
}

} // namespace detail

template <size_t X, size_t Y, size_t... Rest>
constexpr auto static_sum = detail::static_add<size_t, X, Y, Rest...>();

////////////////////////////////////////////////////////////////////////////////
// Forward declaration of buffer storage types and buffer interface.
////////////////////////////////////////////////////////////////////////////////

template <size_t N, typename T, typename Tag>
struct buffer_storage_normal;

template <size_t N, typename T, typename Tag>
struct buffer_storage_secure;

template <size_t N, typename T, typename Tag>
struct buffer_storage_ref;

template <typename Storage>
struct buffer_impl;

////////////////////////////////////////////////////////////////////////////////
// Buffer concepts.
////////////////////////////////////////////////////////////////////////////////

template <typename T>
concept static_buffer =
    std::ranges::sized_range<T> &&
    (std::derived_from<
         T, buffer_impl<buffer_storage_normal<
                T::static_size(), typename T::value_type, typename T::tag>>> ||
     std::derived_from<
         T, buffer_impl<buffer_storage_secure<
                T::static_size(), typename T::value_type, typename T::tag>>> ||
     std::derived_from<
         T, buffer_impl<buffer_storage_ref<
                T::static_size(), typename T::value_type, typename T::tag>>>);

// clang-format off
template <typename T>
concept static_byte_buffer =
    static_buffer<T> &&
    std::same_as<
        std::remove_cv_t<std::ranges::range_value_t<T>>, unsigned char>;

template <typename R>
concept byte_range =
    std::ranges::sized_range<R> &&
    std::same_as<
        std::remove_cv_t<std::ranges::range_value_t<R>>, unsigned char>;
// clang-format on

////////////////////////////////////////////////////////////////////////////////
// Utility functions.
////////////////////////////////////////////////////////////////////////////////

namespace detail {

// Checks value types of the given buffer types. Returns true if all buffer
// types share the same value type, and false otherwise.
template <static_buffer Buffer0, static_buffer Buffer1,
          static_buffer... Buffers>
constexpr auto
check_homogeneity() noexcept -> bool {
    auto f = std::same_as<std::remove_cv_t<typename Buffer0::value_type>,
                          std::remove_cv_t<typename Buffer1::value_type>>;

    if constexpr(sizeof...(Buffers) == 0) {
        return f;
    } else {
        return f && check_homogeneity<Buffer0, Buffers...>();
    }
}

// Checks for possible buffer overflow when trying to fit a buffer of type
// {Buffer0} into a buffer of type {Buffer1} starting from the given {Offset}.
template <size_t Offset, static_buffer Buffer0, static_buffer Buffer1>
constexpr auto
check_buffer_overflow() noexcept -> bool {
    auto same_value_type =
        std::same_as<std::remove_cv_t<typename Buffer0::value_type>,
                     std::remove_cv_t<typename Buffer1::value_type>>;

    auto no_overflow =
        (static_sum<Offset, Buffer0::static_size()> <= Buffer1::static_size());

    return (same_value_type && no_overflow);
}

// Computes the size of the joint buffer.
template <static_buffer Buffer, static_buffer... Buffers>
constexpr auto
compute_joint_buffer_size() noexcept -> size_t {
    if constexpr(sizeof...(Buffers) == 0) {
        return Buffer::static_size();
    } else {
        return static_sum<Buffer::static_size(),
                          compute_joint_buffer_size<Buffers...>()>;
    }
}

} // namespace detail

template <static_buffer Buffer0, static_buffer Buffer1,
          static_buffer... Buffers>
constexpr auto are_homogeneous_buffers =
    detail::check_homogeneity<Buffer0, Buffer1, Buffers...>();

template <size_t Offset, static_buffer Buffer0, static_buffer Buffer1>
constexpr auto no_buffer_overflow =
    detail::check_buffer_overflow<Offset, Buffer0, Buffer1>();

template <static_buffer Buffer, static_buffer... Buffers>
constexpr auto joint_buffer_size =
    detail::compute_joint_buffer_size<Buffer, Buffers...>();

////////////////////////////////////////////////////////////////////////////////
// Buffer tag types.
////////////////////////////////////////////////////////////////////////////////

struct default_buffer_tag {};

template <typename T>
struct wrapped_buffer_tag {};

template <static_buffer Buffer, static_buffer... Buffers>
using joint_buffer_tag = std::conditional_t<
    (sizeof...(Buffers) == 0), typename Buffer::tag,
    std::tuple<wrapped_buffer_tag<typename Buffer::tag>,
               wrapped_buffer_tag<typename Buffers::tag>...>>;

////////////////////////////////////////////////////////////////////////////////
// Byte sequences.
////////////////////////////////////////////////////////////////////////////////

// Mutable sequence.
using mut_byte_sequence = std::span<unsigned char>;

// Immutable sequence.
using byte_sequence = std::span<unsigned char const>;

////////////////////////////////////////////////////////////////////////////////
// Buffer types.
////////////////////////////////////////////////////////////////////////////////

// Main specializations.
template <size_t N, typename T = unsigned char,
          typename Tag = default_buffer_tag>
using buffer = buffer_impl<buffer_storage_normal<N, T, Tag>>;

template <size_t N, typename T = unsigned char,
          typename Tag = default_buffer_tag>
using secure_buf = buffer_impl<buffer_storage_secure<N, T, Tag>>;

template <size_t N, typename T = unsigned char,
          typename Tag = default_buffer_tag>
using buffer_ref = buffer_impl<buffer_storage_ref<N, T, Tag>>;

// Joint buffer types.
template <static_buffer Buffer, static_buffer... Buffers>
using joint_buffer = buffer<joint_buffer_size<Buffer, Buffers...>,
                            std::remove_cv_t<typename Buffer::value_type>,
                            joint_buffer_tag<Buffer, Buffers...>>;

template <static_buffer Buffer, static_buffer... Buffers>
using joint_buffer_secure =
    secure_buf<joint_buffer_size<Buffer, Buffers...>,
               std::remove_cv_t<typename Buffer::value_type>,
               joint_buffer_tag<Buffer, Buffers...>>;

////////////////////////////////////////////////////////////////////////////////
// Buffer reference types.
////////////////////////////////////////////////////////////////////////////////

template <static_buffer T>
using mut_ref =
    buffer_ref<T::static_size(), typename T::value_type, typename T::tag>;

template <static_buffer T>
using ref =
    buffer_ref<T::static_size(), typename T::value_type const, typename T::tag>;

namespace detail {

template <static_buffer Buffer_src, static_buffer Buffer_dst>
using select_ref =
    std::conditional_t<std::is_const_v<Buffer_src> ||
                           std::is_const_v<typename Buffer_src::value_type>,
                       ref<Buffer_dst>, mut_ref<Buffer_dst>>;

} // namespace detail

////////////////////////////////////////////////////////////////////////////////
// Buffer implementation.
////////////////////////////////////////////////////////////////////////////////

template <size_t Offset, static_buffer Buffer_src, static_buffer Buffer_dst0,
          static_buffer... Buffers_dst>
constexpr auto is_valid_buffer_operation =
    (are_homogeneous_buffers<Buffer_src, Buffer_dst0, Buffers_dst...> &&
     no_buffer_overflow<Offset, joint_buffer<Buffer_dst0, Buffers_dst...>,
                        Buffer_src>);

template <static_buffer... Buffers>
constexpr auto are_valid_extraction_target =
    (!std::derived_from<Buffers,
                        buffer_storage_ref<Buffers::static_size(),
                                           typename Buffers::value_type,
                                           typename Buffers::tag>> &&
     ...);

template <size_t Offset, static_buffer Buffer_src, static_buffer Buffer_dst0,
          static_buffer... Buffers_dst>
constexpr auto is_valid_extract_operation =
    (is_valid_buffer_operation<Offset, Buffer_src, Buffer_dst0,
                               Buffers_dst...> &&
     are_valid_extraction_target<Buffer_dst0, Buffers_dst...>);

template <typename Storage>
struct buffer_impl : Storage {
    using value_type = typename Storage::value_type;
    using tag = typename Storage::tag;

    using mut_ref = buffer_ref<Storage::static_size, value_type, tag>;
    using ref = buffer_ref<Storage::static_size, value_type const, tag>;

    static constexpr auto is_noexcept =
        std::is_nothrow_copy_constructible_v<value_type>;

    constexpr auto
    begin() noexcept {
        return data();
    }

    constexpr auto
    begin() const noexcept {
        return data();
    }

    constexpr auto
    end() noexcept {
        return data() + static_size();
    }

    constexpr auto
    end() const noexcept {
        return data() + static_size();
    }

    static constexpr auto
    size() noexcept -> size_t {
        return Storage::static_size;
    }

    static constexpr auto
    static_size() noexcept -> size_t {
        return Storage::static_size;
    }

    constexpr auto&
    operator[](size_t i) noexcept {
        return data()[i];
    }

    constexpr auto&
    operator[](size_t i) const noexcept {
        return data()[i];
    }

    constexpr auto
    data() noexcept {
        return this->data_;
    }

    constexpr auto
    data() const noexcept {
        return static_cast<std::add_const_t<value_type>*>(this->data_);
    }

    template <size_t Offset, static_buffer Buffer, static_buffer... Buffers>
    constexpr void
    copy_into(Buffer& x, Buffers&... rest) const noexcept(is_noexcept) requires(
        is_valid_buffer_operation<Offset, buffer_impl, Buffer, Buffers...>) {
        copy_into_<Offset>(x, rest...);
    }

    template <static_buffer Buffer, static_buffer... Buffers>
    constexpr void
    copy_into(Buffer& x, Buffers&... rest) const noexcept(is_noexcept) requires(
        is_valid_buffer_operation<0, buffer_impl, Buffer, Buffers...>) {
        copy_into<0>(x, rest...);
    }

    template <size_t Offset, static_buffer Buffer, static_buffer... Buffers>
    constexpr auto&
    fill_from(Buffer const& x, Buffers const&... rest) noexcept(
        is_noexcept) requires(is_valid_buffer_operation<Offset, buffer_impl,
                                                        Buffer, Buffers...>) {
        return fill_from_<Offset>(x, rest...);
    }

    template <static_buffer Buffer, static_buffer... Buffers>
    constexpr auto&
    fill_from(Buffer const& x, Buffers const&... rest) noexcept(
        is_noexcept) requires(is_valid_buffer_operation<0, buffer_impl, Buffer,
                                                        Buffers...>) {
        return fill_from<0>(x, rest...);
    }

    template <size_t Offset, static_buffer Buffer, static_buffer... Buffers>
    constexpr auto
    extract() const noexcept(is_noexcept) -> decltype(auto) requires(
        is_valid_extract_operation<Offset, buffer_impl, Buffer, Buffers...>) {
        if constexpr(sizeof...(Buffers) == 0) {
            auto r = Buffer{};
            copy_into_<Offset>(r);

            return r;
        } else {
            auto r = std::tuple<Buffer, Buffers...>{};
            extract_tuple_<Offset, 0>(r);

            return r;
        }
    }

    template <static_buffer Buffer, static_buffer... Buffers>
    constexpr auto
    extract() const noexcept(is_noexcept) -> decltype(auto) requires(
        is_valid_extract_operation<0, buffer_impl, Buffer, Buffers...>) {
        return extract<0, Buffer, Buffers...>();
    }

    template <size_t Offset, static_buffer Buffer, static_buffer... Buffers>
    constexpr auto
    view_as() noexcept -> decltype(auto) requires(
        is_valid_buffer_operation<Offset, buffer_impl, Buffer, Buffers...>) {
        return view_as_<Offset, buffer_impl, Buffer, Buffers...>(*this);
    }

    template <size_t Offset, static_buffer Buffer, static_buffer... Buffers>
    constexpr auto
    view_as() const noexcept -> decltype(auto) requires(
        is_valid_buffer_operation<Offset, buffer_impl, Buffer, Buffers...>) {
        return view_as_<Offset, buffer_impl const, Buffer, Buffers...>(*this);
    }

    template <static_buffer Buffer, static_buffer... Buffers>
    constexpr auto
    view_as() noexcept -> decltype(auto) requires(
        is_valid_buffer_operation<0, buffer_impl, Buffer, Buffers...>) {
        return view_as<0, Buffer, Buffers...>();
    }

    template <static_buffer Buffer, static_buffer... Buffers>
    constexpr auto
    view_as() const noexcept -> decltype(auto) requires(
        is_valid_buffer_operation<0, buffer_impl, Buffer, Buffers...>) {
        return view_as<0, Buffer, Buffers...>();
    }

    operator mut_ref() noexcept {
        return mut_ref{data()};
    }

    operator ref() const noexcept {
        return ref{data()};
    }

private:
    template <size_t Offset, typename Buffer, typename... Buffers>
    constexpr void
    copy_into_(Buffer& x, Buffers&... rest) const noexcept(is_noexcept) {
        std::copy_n(data() + Offset, x.static_size(), x.data());

        if constexpr(sizeof...(Buffers) != 0) {
            copy_into_<Offset + Buffer::static_size()>(rest...);
        }
    }

    template <size_t Offset, typename Buffer, typename... Buffers>
    constexpr auto&
    fill_from_(Buffer const& x, Buffers const&... rest) noexcept(is_noexcept) {
        std::copy_n(x.data(), x.static_size(), data() + Offset);

        if constexpr(sizeof...(Buffers) != 0) {
            fill_from_<Offset + Buffer::static_size()>(rest...);
        }

        return *this;
    }

    template <size_t Offset, typename Buffer_src, typename Buffer_dst0,
              typename... Buffers_dst>
    static constexpr auto
    view_as_(Buffer_src& self) noexcept -> decltype(auto) {
        if constexpr(sizeof...(Buffers_dst) == 0) {
            return detail::select_ref<Buffer_src, Buffer_dst0>{self.data() +
                                                               Offset};
        } else {
            auto r =
                std::tuple<detail::select_ref<Buffer_src, Buffer_dst0>,
                           detail::select_ref<Buffer_src, Buffers_dst>...>{};
            view_as_tuple_<Offset, 0>(self, r);

            return r;
        }
    }

    template <size_t Offset, size_t I, typename Tuple>
    constexpr void
    extract_tuple_(Tuple& t) const noexcept(is_noexcept) {
        copy_into_<Offset>(std::get<I>(t));

        if constexpr((I + 1) < std::tuple_size_v<Tuple>) {
            extract_tuple_<
                Offset + std::tuple_element_t<I, Tuple>::static_size(), I + 1>(
                t);
        }
    }

    template <size_t Offset, size_t I, typename Buffer, typename Tuple>
    static constexpr void
    view_as_tuple_(Buffer& self, Tuple& t) noexcept {
        std::get<I>(t).data_ = self.data() + Offset;

        if constexpr((I + 1) < std::tuple_size_v<Tuple>) {
            view_as_tuple_<
                Offset + std::tuple_element_t<I, Tuple>::static_size(), I + 1>(
                self, t);
        }
    }

    template <typename T>
    friend struct buffer_impl;
};

////////////////////////////////////////////////////////////////////////////////
// Buffer comparison.
////////////////////////////////////////////////////////////////////////////////

template <static_buffer Buffer0, static_buffer Buffer1>
constexpr auto is_valid_buffer_comparison =
    (std::same_as<typename Buffer0::value_type, typename Buffer1::value_type> &&
     std::same_as<typename Buffer0::tag, typename Buffer1::tag> &&
     std::totally_ordered<typename Buffer0::value_type> &&
     (Buffer0::static_size() == Buffer1::static_size()));

template <static_buffer Buffer0, static_buffer Buffer1>
constexpr auto
operator<(Buffer0 const& x, Buffer1 const& y) noexcept
    -> bool requires(is_valid_buffer_comparison<Buffer0, Buffer1>) {
    return std::ranges::lexicographical_compare(x, y);
}

template <static_buffer Buffer0, static_buffer Buffer1>
constexpr auto
operator>(Buffer0 const& x, Buffer1 const& y) noexcept
    -> bool requires(is_valid_buffer_comparison<Buffer0, Buffer1>) {
    return std::ranges::lexicographical_compare(y, x);
}

template <static_buffer Buffer0, static_buffer Buffer1>
constexpr auto
operator<=(Buffer0 const& x, Buffer1 const& y) noexcept
    -> bool requires(is_valid_buffer_comparison<Buffer0, Buffer1>) {
    return !(x > y);
}

template <static_buffer Buffer0, static_buffer Buffer1>
constexpr auto
operator>=(Buffer0 const& x, Buffer1 const& y) noexcept
    -> bool requires(is_valid_buffer_comparison<Buffer0, Buffer1>) {
    return !(x < y);
}

template <static_buffer Buffer0, static_buffer Buffer1>
constexpr auto
operator==(Buffer0 const& x, Buffer1 const& y) noexcept
    -> bool requires(is_valid_buffer_comparison<Buffer0, Buffer1>) {
    return std::ranges::equal(x, y);
}

template <static_buffer Buffer0, static_buffer Buffer1>
constexpr auto
operator!=(Buffer0 const& x, Buffer1 const& y) noexcept
    -> bool requires(is_valid_buffer_comparison<Buffer0, Buffer1>) {
    return !(x == y);
}

////////////////////////////////////////////////////////////////////////////////
// Buffer storage types.
////////////////////////////////////////////////////////////////////////////////

template <size_t N, typename T, typename Tag>
struct buffer_storage_normal {
    static constexpr size_t static_size = N;

    using value_type = T;
    using tag = Tag;

    T data_[N];
};

template <typename T, typename Tag>
struct buffer_storage_normal<0, T, Tag> {
    static constexpr size_t static_size = 0;

    using value_type = T;
    using tag = Tag;

    static constexpr auto data_ = static_cast<value_type*>(nullptr);
};

template <size_t N, typename T, typename Tag>
struct buffer_storage_secure {
    static constexpr size_t static_size = N;

    using value_type = T;
    using tag = Tag;

    ~buffer_storage_secure() {
        auto volatile ptr = data_;
        std::fill_n(ptr, N, T{});
    }

    T data_[N];
};

template <typename T, typename Tag>
struct buffer_storage_secure<0, T, Tag> {
    static constexpr size_t static_size = 0;

    using value_type = T;
    using tag = Tag;

    static constexpr auto data_ = static_cast<value_type*>(nullptr);
};

template <size_t N, typename T, typename Tag>
struct buffer_storage_ref {
    static constexpr size_t static_size = N;

    using value_type = T;
    using tag = Tag;

protected:
    buffer_storage_ref() noexcept : data_{} {
    }

    buffer_storage_ref(T* x) noexcept : data_{x} {
    }

    template <typename Storage>
    friend struct buffer_impl;

    T* data_;
};

////////////////////////////////////////////////////////////////////////////////
// Buffer viewing and joining.
////////////////////////////////////////////////////////////////////////////////

template <size_t Chunk_size, static_buffer Buffer>
constexpr auto
view_buffer_by_chunks(Buffer& x) noexcept
    -> decltype(auto) requires((Buffer::static_size() % Chunk_size) == 0) {
    using view = detail::select_ref<
        Buffer,
        buffer<Chunk_size, typename Buffer::value_type, typename Buffer::tag>>;

    return ([&x]<size_t... Indices>(std::index_sequence<Indices...>) {
        return buffer<sizeof...(Indices), view>{
            x.template view_as<Indices * Chunk_size, view>()...};
    })(std::make_index_sequence<Buffer::static_size() / Chunk_size>{});
}

template <static_buffer Buffer, static_buffer... Buffers>
constexpr auto
join_buffers(Buffer const& x,
             Buffers const&... rest) noexcept(Buffer::is_noexcept)
    -> decltype(auto) {
    auto r = joint_buffer<Buffer, Buffers...>{};
    r.fill_from(x, rest...);

    return r;
}

template <static_buffer Buffer, static_buffer... Buffers>
constexpr auto
join_buffers_secure(Buffer const& x,
                    Buffers const&... rest) noexcept(Buffer::is_noexcept)
    -> decltype(auto) {
    auto r = joint_buffer_secure<Buffer, Buffers...>{};
    r.fill_from(x, rest...);

    return r;
}

////////////////////////////////////////////////////////////////////////////////
// Buffer conversion.
////////////////////////////////////////////////////////////////////////////////

namespace detail {

template <typename T>
concept integer = std::integral<T> && !std::same_as<std::remove_cv_t<T>, bool>;

} // namespace detail

template <detail::integer T>
constexpr auto integer_size = static_sum<
    ((std::numeric_limits<std::make_unsigned_t<T>>::digits / CHAR_BIT)),
    ((std::numeric_limits<std::make_unsigned_t<T>>::digits % CHAR_BIT) != 0)>;

template <detail::integer T, static_byte_buffer Buffer>
constexpr auto is_valid_buffer_conversion = //
    (Buffer::static_size() == integer_size<T>);

template <detail::integer T, static_byte_buffer Buffer>
constexpr void
int_to_buffer(T x, Buffer& buf) noexcept
    requires(is_valid_buffer_conversion<T, Buffer>) {
    for(size_t i = 0; i < integer_size<T>; ++i) {
        buf[i] = static_cast<unsigned char>(
            static_cast<std::make_unsigned_t<T>>(x) >> (i * CHAR_BIT));
    }
}

template <detail::integer T>
constexpr auto
int_to_buffer(T x) noexcept -> decltype(auto) {
    buffer<integer_size<T>> r;
    int_to_buffer(x, r);

    return r;
}

template <detail::integer T, static_byte_buffer Buffer>
constexpr void
buffer_to_int(Buffer const& buf, T& x) noexcept
    requires(is_valid_buffer_conversion<T, Buffer>) {
    using unsigned_type = std::make_unsigned_t<T>;
    auto r = unsigned_type{};

    for(size_t i = 0; i < integer_size<T>; ++i) {
        r |= static_cast<unsigned_type>(buf[i]) << (i * CHAR_BIT);
    }

    x = static_cast<T>(r);
}

template <detail::integer T, static_byte_buffer Buffer>
constexpr auto
buffer_to_int(Buffer const& buf) noexcept -> T
    requires(is_valid_buffer_conversion<T, Buffer>) {
    T r;
    return buffer_to_int(buf, r), r;
}

} // namespace ecstk

#endif // H_639425CCA60E448B9BEB43186E06CA57
