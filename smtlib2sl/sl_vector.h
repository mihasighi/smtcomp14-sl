/* -*- C -*-
 *
 * Generic resizable arrays for the SMT-LIB v2 parser
 *
 * Author: Alberto Griggio <griggio@fbk.eu>
 *
 * Copyright (C) 2010 Alberto Griggio
 *
 * Permission is hereby granted, free of charge, to any person obtaining a
 * copy of this software and associated documentation files (the "Software"),
 * to deal in the Software without restriction, including without limitation
 * the rights to use, copy, modify, merge, publish, distribute, sublicense,
 * and/or sell copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
 * DEALINGS IN THE SOFTWARE.
 */
#ifndef SL_VECTOR_H_
#define SL_VECTOR_H_

#include <stdbool.h>
#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

typedef uint32_t uint_t;

#define SL_VECTOR_DECLARE(name, type)                              \
typedef struct name {                                                \
    type *data_;                                                     \
    uint_t size_;                                                    \
    uint_t capacity_;                                                \
} name;                                                              \
name * name ## _new(void);                                           \
void name ## _delete(name *v);                                       \
void name ## _push(name *v, type elem);                              \
void name ## _pop(name *v);                                          \
void name ## _cup(name *v, type elem);                               \
void name ## _resize(name *v, uint_t newsz);                         \
void name ## _reserve(name *v, uint_t cap);                          \
void name ## _clear(name *v);                                        \
void name ## _copy(name *dest, const name *src);                     \
void name ## _swap(name *v1, name *v2);                              \
bool name ## _equal(const name *v1, const name *v2);

#define SL_VECTOR_SIZE(v) ((v)->size_)
#define SL_VECTOR_CAPACITY(v) ((v)->capacity_)
#define SL_VECTOR_ARRAY(v) ((v)->data_)

#define sl_vector_size(v) SL_VECTOR_SIZE(v)
#define sl_vector_capacity(v) SL_VECTOR_CAPACITY(v)
#define sl_vector_at(v, i) (SL_VECTOR_ARRAY(v)[(i)])
#define sl_vector_last(v) sl_vector_at(v, SL_VECTOR_SIZE(v)-1)
#define sl_vector_first(v) sl_vector_at(v, 0)
#define sl_vector_array(v) SL_VECTOR_ARRAY(v)
#define sl_vector_empty(v) (0 == sl_vector_size(v))

#define SL_VECTOR_DEFINE(name, type) \
name *name ## _new(void)                                \
{                                                                       \
    name *ret = (name *)malloc(sizeof(name)); \
    ret->data_ = NULL;                                                  \
    ret->size_ = 0;                                                     \
    ret->capacity_ = 0;                                                 \
                                                                        \
    return ret;                                                         \
}                                                                       \
                                                                        \
                                                                        \
void name ## _delete(name *v)                           \
{                                                                       \
    if (v->data_ != NULL) {                                             \
        free(v->data_);                                                 \
    }                                                                   \
    free(v);                                                            \
}                                                                       \
                                                                        \
                                                                        \
void name ## _push(name *v, type elem)              \
{                                                                       \
    assert(v != NULL);                                                  \
    if (v->size_ >= v->capacity_) {                                     \
        name ## _reserve(v, v->capacity_ ? v->capacity_ * 2 : 2); \
    }                                                                   \
    v->data_[v->size_++] = elem;                                        \
}                                                                       \
                                                                        \
                                                                        \
void name ## _pop(name *v)                              \
{                                                                       \
    assert(v->size_ > 0);                                               \
    --v->size_;                                                         \
}                                                                       \
                                                                        \
                                                                        \
void name ## _cup(name *v, type elem)                \
{                                                                       \
    assert(v != 0);                                                     \
    for (uint_t i = 0; i < v->size_; i++)                               \
      if (v->data_[i] == elem) return;                                  \
    name ## _push (v, elem);                                            \
}                                                                       \
                                                                        \
                                                                        \
void name ## _resize(name *v, uint_t newsz)             \
{                                                                       \
    if (v->size_ >= newsz) {                                            \
        v->size_ = newsz;                                               \
    } else {                                                            \
        uint_t i;                                                       \
        name ## _reserve(v, newsz);                               \
        for (i = v->size_; i < newsz; ++i) {                            \
            v->data_[i] = 0;                                            \
        }                                                               \
        v->size_ = newsz;                                               \
    }                                                                   \
}                                                                       \
                                                                        \
                                                                        \
void name ## _reserve(name *v, uint_t cap)              \
{                                                                       \
    assert(cap > 0);                                                    \
                                                                        \
    if (v->capacity_ < cap) {                                           \
        v->data_ = (type *)realloc(v->data_, sizeof(type)*cap); \
        v->capacity_ = cap;                                             \
    }                                                                   \
}                                                                       \
                                                                        \
                                                                        \
void name ## _clear(name *v)                            \
{                                                                       \
    v->size_ = 0;                                                       \
    v->capacity_ = 0;                                                   \
    if (v->data_) {                                                     \
        free(v->data_);                                                 \
        v->data_ = NULL;                                                \
    }                                                                   \
}                                                                       \
                                                                        \
                                                                        \
void name ## _copy(name *dest, const name *src)                         \
{                                                                       \
    name ## _resize(dest, src->size_);                                  \
    dest->size_ = src->size_;                                           \
    if (src->data_ != NULL) {                                          \
        memcpy(dest->data_, src->data_, sizeof(type) * src->size_);     \
    }                                                                   \
}                                                                       \
                                                                        \
                                                                        \
void name ## _swap(name *v1, name *v2)                                  \
{                                                                       \
    uint_t tmp1;                                                        \
    type *tmp2;                                                         \
                                                                        \
    tmp1 = v1->size_;                                                   \
    v1->size_ = v2->size_;                                              \
    v2->size_ = tmp1;                                                   \
                                                                        \
    tmp1 = v1->capacity_;                                               \
    v1->capacity_ = v2->capacity_;                                      \
    v2->capacity_ = tmp1;                                               \
                                                                        \
    tmp2 = v1->data_;                                                   \
    v1->data_ = v2->data_;                                              \
    v2->data_ = tmp2;                                                   \
}                                                                       \
                                                                        \
bool name ## _equal(const name *v1, const name *v2)                     \
{                                                                       \
    assert(NULL != v1);                                                 \
    assert(NULL != v2);                                                 \
    size_t size = sl_vector_size(v1);                                 \
    if (sl_vector_size(v2) != size)                                   \
        return false;                                                   \
                                                                        \
    for (size_t i = 0; i < size; ++i)                                   \
    {                                                                   \
        if (sl_vector_at(v1, i) != sl_vector_at(v2, i))             \
            return false;                                               \
    }                                                                   \
                                                                        \
    return true;                                                        \
}

#endif /* SL_VECTOR_H_ */
