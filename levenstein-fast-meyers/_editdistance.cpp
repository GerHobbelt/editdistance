// -------
// License
// -------
//
// It is released under the MIT license.
//
//     Copyright (c) 2013 Hiroyuki Tanaka
//
//     Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:
//
//     The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
//
//     THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.


#include <cstdlib>
#include <cstring>
#include <string>
#include <map>
#include <vector>
#include <iostream>
#include <bitset>
#include <algorithm>

#include "./_editdistance.h"

using namespace std;

template<typename T, typename TVALUE>
unsigned int edit_distance_bpv(T &cmap, int64_t const *vec, size_t const &vecsize, unsigned int const &tmax, unsigned int const &tlen) {
    int D = tmax * 64 + tlen;
    TVALUE D0, HP, HN, VP, VN;
    uint64_t top = (1LL << (tlen - 1));  // applied to the trailing vector
    uint64_t lmb = (1LL << 63);

    for(size_t i = 0; i <= tmax; ++i) {
        VP[i] = 0;
        VN[i] = 0;
    }
    for(size_t i = 0; i < tmax; ++i) 
		VP[i] = ~0;
    for(size_t i = 0; i < tlen; ++i) 
		VP[tmax] |= (1LL << i);
    for(size_t i = 0; i < vecsize; ++i) {
        TVALUE &PM = cmap[vec[i]];
        for(unsigned int r = 0; r <= tmax; ++r) {
            uint64_t X = PM[r];
            if (r > 0 && (HN[r - 1] & lmb)) 
				X |= 1LL;
            D0[r] = (((X & VP[r]) + VP[r]) ^ VP[r]) | X | VN[r];
            HP[r] = VN[r] | ~(D0[r] | VP[r]);
            HN[r] = D0[r] & VP[r];
            X = (HP[r] << 1LL);
            if (r == 0 || HP[r - 1] & lmb) 
				X |= 1LL;
            VP[r] = (HN[r] << 1LL) | ~(D0[r] | X);
            if (r > 0 && (HN[r - 1] & lmb)) 
				VP[r] |= 1LL;
            VN[r] = D0[r] & X;
        }
        if (HP[tmax] & top) 
			++D;
        else if (HN[tmax] & top) 
			--D;
    }
    return D;
}


/// http://handasse.blogspot.com/2009/04/c_29.html 
///
/// (comment/log-article below has been google-translated and minimally post-edited)
/*
C++: Algorithm to find edit distance

4/29/2009

Edit distance is a numerical value that indicates how different two strings are, and often refers to Levenshtein distance . It calculates the minimum number of operations necessary to insert, delete, and replace characters as one operation. For example, if you want to find the edit distance between kitten and sitting, you can change kitten to sitting with three operations as shown below, so the edit distance will be 3.

1. sitten (replace k with s)
2. sittin (replace e with i)
3. sitting (insert g)

So this time, I tried implementing several algorithms to find the edit distance in C++.

Dynamic Programming

Probably the most common algorithm for determining edit distance is dynamic programming. The calculation time is O(mn) and it is easy. The code written in C++ is shown below. The constant SIZE that appears in the code should be determined appropriately according to the character string being handled. Although it is possible to allocate memory dynamically, processing will be slower, so it is more efficient to allocate memory in advance.

*/

int edit_distance_dp_basic(const string& str1, const string& str2)
{
    static int d[SIZE][SIZE];

    for (int i = 0; i < str1.size() + 1; i++) 
		d[i][0] = i;
    for (int i = 0; i < str2.size() + 1; i++) 
		d[0][i] = i;
    for (int i = 1; i < str1.size() + 1; i++)
        for (int j = 1; j < str2.size() + 1; j++)
            d[i][j] = min(min(d[i-1][j], d[i][j-1]) + 1, d[i-1][j-1] + (str1[ i-1] == str2[j-1] ? 0 : 1));

    return d[str1.size()][str2.size()];
} 

/*

Addition of O(ND) algorithm (2009/7/8): 

As pointed out in the comments, I researched the O(ND)/O(NP) algorithm and found that the minimum number of operations using only insertion and deletion (In the paper, the algorithm was to find the shortest edit "script"). In other words, replacement involves two steps: deletion and insertion. The ternary operator part of the above dynamic programming can be changed from (str1[i-1] == str2[j-1] ? 0 : 1) to (str1[i-1] == str2[j-1] ? 0 : 2) to obtain the same number of operations. 

Next, we will show the O(ND) algorithm. N is the sum of the two number of elements (m, n), and D is the edit distance. In other words, the smaller the edit distance, the faster the calculation will be. The original paper is EW Myers. An O(ND) difference algorithm and its variations. Algorithmica 1, 251-266 (1986), and the explanation in Japanese uses the document comparison algorithm as well as the O(NP) algorithm described later. become. The code is shown below. 

*/

int edit_distance_ond(const string& str1, const string& str2)
{
    static int V[SIZE];
    int x, y;
    int offset = str1.size();
    V[offset + 1] = 0;

    for (int D = 0; D <= str1.size() + str2.size(); D++) {
        for (int k = -D; k <= D; k += 2) {
            if (k == -D || k != D && V[k-1+offset] < V[k+1+offset]) 
				x = V[k+1+offset];
            else 
				x = V[k-1+offset] + 1;
            y = x - k;
            while (x < str1.size() && y < str2.size() && str1[x] == str2[y]) {
                x++;
                y++;
            }
            V[k+offset] = x;
            if (x >= str1.size() && y >= str2.size()) 
				return D;
        }
    }

    return -1;
} 

/*

O(NP) algorithm

The O(NP) algorithm is a further improvement of O(ND). P is expressed as P=(D-(mn))/2, where m and n (m >= n) are the number of elements, respectively. From experience, it seems to be about half of O(ND). The original paper is S. Wu, U. Manber, and G. Myers. An O(NP) sequence comparison algorithm. Information Processing Letter . 35 (6) 317-332 (1990). The code is shown below.

*/

int snake(int k, int y, const string& str1, const string& str2)
{
    int x = y - k;

    while (x < str1.size() && y < str2.size() && str1[x] == str2[y]) {
        x++;
        y++;
    }

    return y;
}

int edit_distance_onp(const string& str1, const string& str2)
{
    // required: s1->size() <= s2->size()
    const string* const s1 = str1.size() > str2.size() ? &str2 : &str1;
    const string* const s2 = str1.size() > str2.size() ? &str1 : &str2;
    static int fp[SIZE];
    int x, y, k, p;
    int offset = s1->size() + 1;
    int delta = s2->size() - s1->size();
    for (int i = 0; i < SIZE; i++) 
		fp[i] = -1;

    for (p = 0; fp[delta + offset] != s2->size(); p++) {
        for(k = -p; k < delta; k++)
            fp[k + offset] = snake(k, max(fp[k-1+offset] + 1, fp[k+1+offset]), *s1, *s2);
        for(k = delta + p; k > delta; k--)
            fp[k + offset] = snake(k, max(fp[k-1+offset] + 1, fp[k+1+offset]), *s1, *s2);
        fp[delta + offset] = snake(delta, max(fp[delta-1+offset] + 1, fp[delta+1+offset]), *s1, *s2);
    }

    return delta + (p - 1) * 2;
} 

/*

Bit-parallel method

Finally, we will show the bit-parallel method. This applies dynamic programming, and by using bit operations, parallel processing is possible and calculations can be performed in O(m/wn). Here, w indicates the word length. In other words, if the number of elements m is equal to or less than the word length w, the calculation can be done in O(n), making it possible to process very quickly. The original paper is G. Myers. A fast bit-vector algorithm for approximate string matching based on dynamic progamming. JACM , 46 (3) 395-415, (1999) . The code is shown below.

*/

template<typename T>
int edit_distance_bit(const string& str1, const string& str2)
{
    char s1[sizeof(T) * 8] = { ' ' };
    char s2[sizeof(T) * 8] = { ' ' };
    char *p1, *p2;
    // required: str1.size() >= str2.size()
    if (str1.size() >= str2.size()) { 
		p1 = s1; 
		p2 = s2; 
	}
    else { 
		p1 = s2; 
		p2 = s1; 
	}
    copy(str1.begin(), str1.end(), p1 + 1);
    copy(str2.begin(), str2.end(), p2 + 1);
    int m = strlen(s1);
    int n = strlen(s2);

    const T ONE = 1;
    T Peq[256] = { 0 };
    T Pv, Eq, Xv, Xh, Ph, Mh;
    T Mv = 0;
    int Score = m;

    for (int i = 0; i < m; i++) {
        Peq[s1[i]] |= ONE << i;
        Pv |= (ONE << i);
    }
    for (int j = 0; j < n; j++) {
        Eq = Peq[s2[j]];
        Xv = Eq | Mv;
        Xh = (((Eq & Pv) + Pv) ^ Pv) | Eq;
        Ph = Mv | ~(Xh | Pv);
        Mh = Pv & Xh;
        if (Ph & (ONE << (m - 1))) 
			Score++;
        else if (Mh & (ONE << (m - 1))) 
			Score--;
        Ph <<= ONE;
        Pv = (Mh << ONE) | ~(Xv | Ph);
        Mv = Ph & Xv;
    }

    return Score;
}

/* 
Incidentally, I tried using C++'s bitset to be able to perform operations on any number of bits. Bitset allows normal bitwise operations in most cases, so the code is not much different from the code above. However, since there is no addition operation available, we provided operator+() using operator overload. However, using bitset may not make much sense since you will lose the high-speed processing of bit operations. The code is below.

*/

template<size_t N>
const bitset<N> operator+(const bitset<N>& lhs, const bitset<N>& rhs)
{
    bitset<N> a(lhs), b(rhs), ret(lhs ^ rhs);

    for (b = (a & b) << 1, a = ret; b.any(); b = (a & b) << 1, a = ret) 
		ret ^= b;

    return ret;
}

template<size_t N>
int edit_distance_bitset(const string& str1, const string& str2)
{
    char s1[N] = { ' ' };
    char s2[N] = { ' ' };
    char *p1, *p2;
    // required: str1.size() >= str2.size()
    if (str1.size() >= str2.size()) { 
		p1 = s1; 
		p2 = s2; 
	}
    else { 
		p1 = s2; 
		p2 = s1; 
	}
    copy(str1.begin(), str1.end(), p1 + 1);
    copy(str2.begin(), str2.end(), p2 + 1);
    int m = strlen(s1);
    int n = strlen(s2);

    const bitset<N> ONE(1);
    bitset<N> Peq[256];
    bitset<N> Pv, Mv, Eq, Xv, Xh, Ph, Mh;
    int Score = m;

    for (int i = 0; i < m; i++) {
        Peq[s1[i]] |= ONE << i;
        Pv |= (ONE << i);
    }
    for (int j = 0; j < n; j++) {
        Eq = Peq[s2[j]];
        Xv = Eq | Mv;
        Xh = (((Eq & Pv) + Pv) ^ Pv) | Eq;
        Ph = Mv | ~(Xh | Pv);
        Mh = Pv & Xh;
        if ((Ph & (ONE << (m - 1))).any()) 
			Score++;
        else if ((Mh & (ONE << (m - 1))).any()) 
			Score--;
        Ph <<= 1;
        Pv = (Mh << 1) | ~(Xv | Ph);
        Mv = Ph & Xv;
    }

    return Score;
} 

/*

Speed ​​Comparison

Now, I actually measured how fast these algorithms are and how much of a difference there is. The environment was Windows XP, Intel Core2 6600 @ 2.4GHz, RAM 2GB, and it was compiled as "cl edist_test.cpp /EHsc /O2". The results are as follows; the bit-parallel method is still the fastest for string lengths less than the bit length. In this result, the calculation was completed in less than 1/20th the time of dynamic programming. Next was O(NP), followed by O(ND) and dynamic programming. Speaking of slow, the bit-parallel method using bitset was also slow, but it was still faster than dynamic programming. Also, the speed varies greatly depending on the string length and its combination, so please consider this result as an example. Incidentally, the character string is the DNA base sequence (acgt).

String 1: agtcaaaagtcagtcagtcagtcagtcacagtcagaaggcatccaaccga
String 2: ccgttagtcagaaacagtcagtcagtcagtcagtccagtcttaggcccgga

Dynamic programming:
2.859 seconds for 100,000 repetitions

O(ND) algorithm:
0.500 seconds for 100,000 repetitions

O(NP) algorithm:
0.359 seconds for 100,000 repetitions

Bit parallel method (unsigned long long: 64 bits):
0.125 seconds for 100,000 repetitions

Bit parallel method (bitset: 60 bits):
1.281 seconds for 100,000 repetitions

For reference, the code used for measurement is shown below.

*/

void run(int (*func)(const string&, const string&), const string& arg1, const string& arg2, int num, const string& msg)
{
    clock_t start, finish;

    start = clock();
    for (int i = 0; i < num - 1; i++) 
		(*func)(arg1, arg2);
    cout << msg << " : " << (*func)(arg1, arg2) << endl;
    finish = clock();
    cout << "Time: " << (double)(finish - start) / CLOCKS_PER_SEC << "s (" << num << " times)" << endl;
    cout << endl;
}

int main()
{
    string str1 = "agtcaaaagtcagtcagtcagtcagtcacagtcagaaggcatccaaccga";
    string str2 = "ccgttagtcagaaacagtcagtcagtcagtcagtccagtcttaggcccgga";

    cout << str1 << endl;
    cout << str2 << endl;
    run(edit_distance_dp_basic, str1, str2, 100000, "dp ");
    run(edit_distance_ond, str1, str2, 100000, "ond ");
    run(edit_distance_onp, str1, str2, 100000, "onp ");
    run(edit_distance_bit<unsigned long long>, str1, str2, 100000, "bit ");
    run(edit_distance_bitset<60>, str1, str2, 100000, "bitset");

    return 0;
}

/*

By the way, the edit distance varies slightly depending on the algorithm, but I wonder if this is unavoidable.

As I wrote above, should one operation be "insertion, deletion, replacement" (dynamic programming, bit parallel method) or "insertion, deletion" (O(ND)/O(NP) algorithm)? It was the difference. Fixed some bugs as well.

---------

t98907's comment...

>The edit distance varies slightly depending on the algorithm, but this can't be helped.

7/7/09 08:37

------

Posted by nox …

Thank you for your comment. Thanks to you, I was inspired to read the paper properly.

In dynamic programming and bit-parallel methods, insertions, deletions, and substitutions each cost 1; in O(ND)/O(NP) algorithms, insertions and deletions each cost 1, and replacements become deletions and insertions, which cost 2. It becomes. In the paper, it was called shortest edit "script", and it was clearly written that the only operations were deletion and insertion.

I have corrected the text to address this issue. I also squashed a bug.
8/7/09 01:55

------

Anonymous's comment...

This seems like an old article, but I was curious so I commented.

If we give completely different strings to the code shown in the O(ND) algorithm (for example, "a" and "b"),
V[k-1+offset] seems to become a negative index, but what is that?

------

*/












/// c.f. http://handasse.blogspot.com/2009/04/c_29.html 
unsigned int edit_distance_dp(int64_t const *str1, size_t const size1, int64_t const *str2, size_t const size2) {
    // Fixed-length arrays are faster than vectors, but the size cannot be fixed because they are only called for insurance when the string is long.
    vector< vector<uint32_t> > d(2, vector<uint32_t>(size2 + 1));
    d[0][0] = 0;
    d[1][0] = 1;
    for (size_t i = 0; i < size2 + 1; i++) 
		d[0][i] = i;
    for (size_t i = 1; i < size1 + 1; i++) {
        d[i&1][0] = d[(i-1)&1][0] + 1;
        for (size_t j = 1; j < size2 + 1; j++) {
            d[i&1][j] = min(min(d[(i-1)&1][j], d[i&1][j-1]) + 1, d[(i-1)&1][j-1] + (str1[i-1] == str2[j-1] ? 0 : 1));
        }
    }
    return d[size1&1][size2];
}

template<typename T>
bool edit_distancec_dp(T const *str1, size_t const size1, T const *str2, size_t const size2, unsigned int const thr) {
    vector< vector<uint32_t> > d(2, vector<uint32_t>(size2 + 1));
    d[0][0] = 0;
    d[1][0] = 1;
    for (size_t i = 0; i < size2 + 1; i++) d[0][i] = i;
    for (size_t i = 1; i < size1 + 1; i++) {
        d[i&1][0] = d[(i-1)&1][0] + 1;
        bool below_thr = false;
        for (size_t j = 1; j < size2 + 1; j++) {
            d[i&1][j] = min(min(d[(i-1)&1][j], d[i&1][j-1]) + 1, d[(i-1)&1][j-1] + (str1[i-1] == str2[j-1] ? 0 : 1));
            if (d[i%1][j] <= thr) {
                below_thr = true;
            }
        }
        if (!below_thr) {
            return false;
        }
    }
    return d[size1&1][size2] <= thr;
}


template <size_t N>
struct varr {
    uint64_t arr_[N];
    uint64_t & operator[](size_t const &i) {
        return arr_[i];
    }
};


template<size_t N>
unsigned int edit_distance_map_(int64_t const *a, size_t const asize, int64_t const *b, size_t const bsize) {
    typedef map<int64_t, varr<N> > cmap_v;
    cmap_v cmap;
    unsigned int tmax = (asize - 1) >> 6;
    unsigned int tlen = asize - tmax * 64;
    for (size_t i = 0; i < tmax; ++i) {
        for (size_t j = 0; j < 64; ++j) 
			cmap[a[i * 64 + j]][i] |= (1LL << j);
    }
    for (size_t i = 0; i < tlen; ++i) 
		cmap[a[tmax * 64 + i]][tmax] |= (1LL << i);
    return edit_distance_bpv<cmap_v, typename cmap_v::mapped_type>(cmap, b, bsize, tmax, tlen);
}


unsigned int edit_distance(const int64_t *a, const unsigned int asize, const int64_t *b, const unsigned int bsize) {
    if (asize == 0) 
		return bsize;
    else if (bsize == 0) 
		return asize;
    // The one with the larger number of elements is a
    int64_t const *ap, *bp;
    unsigned int const *asizep, *bsizep;
    if (asize < bsize) {
		ap = b;
		bp = a;
		asizep = &bsize;
		bsizep = &asize;
	}
    else {
		ap = a;
		bp = b;
		asizep = &asize;
		bsizep = &bsize;
	}
    // Find out the required array size
    size_t vsize = ((*asizep - 1) >> 6) + 1;  // 1 up to 64, 2 up to 128, ...
    // 	If the limit that can be achieved with bit-parallel is exceeded, the smaller number of elements is set as a.
    if (vsize > 10) {
        int64_t const *_ = ap;
        unsigned int const *__ = asizep;
        ap = bp;
		bp = _;
		asizep = bsizep;
		bsizep = __;
        vsize = ((*asizep - 1) >> 6) + 1;
    }

    if     (vsize == 1)  return edit_distance_map_<1>(ap, *asizep, bp, *bsizep);
    else if(vsize == 2)  return edit_distance_map_<2>(ap, *asizep, bp, *bsizep);
    else if(vsize == 3)  return edit_distance_map_<3>(ap, *asizep, bp, *bsizep);
    else if(vsize == 4)  return edit_distance_map_<4>(ap, *asizep, bp, *bsizep);
    else if(vsize == 5)  return edit_distance_map_<5>(ap, *asizep, bp, *bsizep);
    else if(vsize == 6)  return edit_distance_map_<6>(ap, *asizep, bp, *bsizep);
    else if(vsize == 7)  return edit_distance_map_<7>(ap, *asizep, bp, *bsizep);
    else if(vsize == 8)  return edit_distance_map_<8>(ap, *asizep, bp, *bsizep);
    else if(vsize == 9)  return edit_distance_map_<9>(ap, *asizep, bp, *bsizep);
    else if(vsize == 10) return edit_distance_map_<10>(ap, *asizep, bp, *bsizep);
    return edit_distance_dp(ap, *asizep, bp, *bsizep);  // dynamic programmingに任せる
}

bool edit_distance_criterion(const int64_t *a, const unsigned int asize, const int64_t *b, const unsigned int bsize, const unsigned int thr) {
    if(asize == 0) return bsize <= thr;
    if(bsize == 0) return asize <= thr;
    // 要素数の大きいほうがa
    int64_t const *ap, *bp;
    unsigned int const *asizep, *bsizep;
    if(asize < bsize) ap = b, bp = a, asizep = &bsize, bsizep = &asize;
    else ap = a, bp = b, asizep = &asize, bsizep = &bsize;
    // 必要な配列サイズを調べる
    size_t vsize = ((*asizep - 1) >> 6) + 1;  // 64までは1, 128までは2, ...
    // bit-parallelでできそうな限界を超えたら要素数の小さい方をaとする。
    if(vsize > 10) {
        int64_t const *_ = ap;
        unsigned int const *__ = asizep;
        ap = bp, bp = _, asizep = bsizep, bsizep = __;
        vsize = ((*asizep - 1) >> 6) + 1;
    }

    return edit_distancec_dp<int64_t>(ap, *asizep, bp, *bsizep, thr);  // dynamic programmingに任せる
}




