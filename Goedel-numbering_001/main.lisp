;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 
;; This program implements routines for encoding symbols as Goedel
;; numbers and decoding such numbers as symbols.
;; 
;; 
;; Concepts
;; ========
;; In the following, a disquisition of a select set of basic terms shall
;; be adduced.
;; 
;; == PRIME NUMBERS ==
;; Prime numbers embrace a subset of integers greater than or equal to 2
;; which are only divisible without a rest by two values:
;;   (i)  themselves
;;   (ii) the number 1.
;; While some definitions encompass the number 1 as a member, at least
;; in our construe the predicament arising from this extension encumbers
;; the topic with unnecessary intricacies.
;; 
;; == POWERS ==
;; The exponentiation or power operation defines a particular concept
;; of the standard multiplication, formulated as
;;   b^e
;; where a real-valued basis b is raised to the real-valued power or
;; exponent e, signifying that b is multiplied e times by itself. For
;; instance:
;; 
;;    2^5 = 2 * 2 * 2 * 2 * 2
;;          -----------------
;;                  ^
;;          the number 2 is multiplied 5 times by itself.
;; 
;; A special convention resides in an exponent of zero (0), in which
;; case the result is defined to always produce the result 1. Hence:
;;   2^0 = 1.
;; For the sake of our purposes, we restrict in this document both the
;; base b and the exponent (power) to nonnegative integers greater than
;; or equal to 0.
;; 
;; == FACTORIZATION ==
;; Factorization in general describes the representation of a number by
;; two or more factors that multiply into the original value. A number
;; is thus considered the production of multiplications and "split"
;; into its constituents, the factors. Frequently, the same original
;; object can be represented by different factor combinations. For
;; example:
;;   
;;   40 = 1 * 40 = 40 * 1
;;      = 2 * 20 = 20 * 2
;;      = 4 * 10 = 10 * 4
;;      = 5 *  8 =  8 * 5
;; 
;; Note that, if tallying the number of ways to factorize a number,
;; multiplication is commutative, that means, the order of its operands
;; is negligible; hence, (4 * 10) is equivalent to (10 * 4). The
;; corollary of this conditions that actually there exist four
;; possibilities for representing the number 40, not eight.
;; 
;; == PRIME FACTORIZATION ==
;; A significant application thereof, the FUNDAMENTAL THEOREM OF
;; ARITHMETIC postulates:
;;   
;;   Any integer greater than 1 either constitute a prime number itself,
;;   or can be formulated as a product of prime numbers in exactly one
;;   unique fashion.
;; 
;; This particular ilk is known as prime factorization. A throughout
;; apprehension may require a few apostils:
;;   
;;   (a) A prime number may occur more than one time in the
;;       factorization. For example:
;;         160 = 2 * 2 * 2 * 2 * 2 * 5
;;             = 2^5               * 9.
;;   (b) The order of the prime constituents --- taking the
;;       commutativity of multiplication into account --- is ignorable.
;;       Formulated generally, we obtain:
;;         a * b = b * a
;; 
;; If we return to our previous example of the number 40 being subject
;; to an analyzation, we following general factorization has been
;; exercised:
;;   
;;   40 = 1 * 40 = 40 * 1
;;      = 2 * 20 = 20 * 2
;;      = 4 * 10 = 10 * 4
;;      = 5 *  8 =  8 * 5
;; 
;; The prime factorization, unique and thus a single solution, would
;; comprise:
;;   
;;   40 = 2 * 2 * 2 * 5 = 2^3 * 5
;; 
;; Please note that, with respect to our above two observations
;;   
;;   (a) The prime number 2 occurs multiple times, namely twice:
;;         2 * 2 * 2 = 2^3.
;;   (b) The order of prime constituents obeys commutativity:
;;           2 * 2 * 2 * 5
;;         = 2 * 2 * 5 * 2
;;         = 2 * 5 * 2 * 2
;;         = 5 * 2 * 2 * 2
;;       All these four variants tally as one combination.
;; 
;; Summarized in simple terms: There exists exactly one combination of
;; prime numbers for representing any nonnegative integer, including
;; prime numbers themselves. A prime number may contribute more than
;; once to this combination.
;; 
;; 
;; Goedel Encoding
;; ===============
;; The sections following below describe the process for encoding a
;; sequence of plaintext symbols as a single positive integer number,
;; known as the Goedel number.
;; 
;; == TERMINOLOGY ==
;; The following apercu shall establish a locality for reference if
;; overwhelmed in the face of future symbolic description:
;;   
;;   L  | The alphabet defining the valid symbols. Its elements are
;;      | enumerated as (l[1], l[2], ...).
;;   ---+---------------------------------------------------------------
;;   C  | The set of possible symbol codes, each mapping to one element
;;      | of the alphabet L. The members of C are exclusively positive
;;      | integer numbers greater than or equal to 1. They enumerate
;;      | as (c[1], c[2], ...).
;;   ---+---------------------------------------------------------------
;;   E  | A mapping which associates with each plaintext symbol of the
;;      | alphabet L exactly one symbol code of the set C.
;;      | The function can be described as:
;;      |   E: L -> C
;;      | When encoding an element l we obtain a symbol code c:
;;      |   E(l) = c, where l in L and c in C.
;;   
;;   N  | The number of elements in the sequence to Goedel-encode.
;;   ---+---------------------------------------------------------------
;;   S  | The sequence of plaintext symbols to Goedel-encode.
;;      | Each element s[i] must be present in the alphabet L.
;;      | The sequence consists of N members, that is, S can be
;;      | described as:
;;      |    S = (s[1], s[2], ..., s[i], ..., s[N]), with s[i] in L.
;;   ---+---------------------------------------------------------------
;;   T  | The sequence of symbol codes which appertain to the plaintext
;;      | sequence S.
;;      | Each element t[i] from T must be present in the set of
;;      | possible symbol codes C.
;;      | Each element t[i] encodes the element s[i] from S at the i-th
;;      | position in S, with i in [1, N], according to the mappings
;;      | defined in the encoding table E, that is:
;;      |   t[i] = E[s[i]], with t[i] in T and also t[i] in C.
;;      | Logically, T contains N members, and thus enumerates as:
;;      |   T = (t[1], t[2], ..., t[i], ..., t[N]), with t[i] in C.
;;   ---+---------------------------------------------------------------
;;   P  | The sequence of the first N prime numbers.
;;      | The members are thus enumerated:
;;      |   P = (p[1], p[2], ..., p[i], ... p[N])
;;      | The elements are defined, thus always the same, and follow
;;      | the pattern
;;      |   P = (2, 3, 5, 7, 11, ...)
;;   ---+---------------------------------------------------------------
;;   PS | A sequence of N elements, where any element ps[i] contains the
;;      | exponentiation of the prime number p[i] raised to the symbol
;;      | code t[i], with p[i] in P and t[i] in T.
;;      |   PS = (ps[1], ps[2], ..., ps[i], ..., ps[N])
;;      | The elements are thus:
;;      |   PS = (p[1]^t[1], p[2]^t[2], ..., p[i]^t[i], ..., p[N]^t[N])
;;   ---+---------------------------------------------------------------
;;   G  | The resulting Goedel number which encodes the plaintext
;;      | sequence S.
;;      | It is the product of the N elements from PS, that is:
;;      |   G = ps[1]      * ps[2]      * ... * ps[i]      * ... * ps[N]
;;      |     =  p[1]^t[1] *  p[2]^t[2] * ... *  p[i]^t[i] * ... *  p[N]^t[N]
;;      | The Goedel number is always an integer number greater than or
;;      | equal to 1.
;; 
;; == APERCU ==
;; Furnished with the foundational gnarity and the terminological
;; conventions, these appurtenances shall now conjoin into an overview
;; concerning the process of Goedel-encoding.
;; 
;; Given:
;;   - An alphabet L encompassing the valid plaintext symbols l[i].
;;   - An encoding table E which unambiguously maps to each alphabet
;;     symbol l[i] an integer number greater than or equal to 1, known
;;     as the symbol code c[i]. The set of all symbol codes shall be
;;     named C. The mapping is thus formulated:
;;       E: l[i] -> c[i], with l[i] in L and c[i] in C.
;;   - A finite sequence S composed of N plaintext symbols which can be
;;     found in the alphabet L:
;;       S = (s[1], s[2], ..., s[i], ..., s[N]), with s[i] in L.
;; 
;; Task:
;;   - The sequence S of plaintext symbols shall be Goedel-encoded,
;;     that is, mapped to a single positive integer number.
;; 
;; Process:
;;   (1) Calculate for the input sequence S with its N elements
;;         S = (s[1], s[2], ..., s[i], ..., s[N])
;;       an equinumerant sequence T with
;;         T = (t[1], t[2], ..., t[i], ..., t[N]),
;;       where each plaintext symbol s[i] is substituted by its code
;;       c[s[i]] according to the encoding table E, assigning
;;         t[i] = E(s[i]).
;;       Concretely, T is defined as:
;;         T = (t[1], t[2], ..., t[i], ..., t[N]), with t[i] in C,
;;       as C represents the set of symbol codes in the mapping E.
;;   (2) Compute a sequence P of the the first N prime numbers:
;;         P = (p[1], p[2], ..., p[i], ..., p[N]),
;;       with p[i] being a prime number.
;;       The sequence P is thus of the pattern
;;         P = (2, 3, 5, 7, 11, ...).
;;   (3) Compute the sequence PS of N elements by calculating for each
;;       element ps[i] the power of the i-th prime number p[i] raised
;;       to the i-th symbol code t[i]:
;;         PS = (ps[1],      ps[2],      ..., ps[i],      ..., ps[N])
;;            = ( p[1]^t[1],  p[2]^t[2], ...,  p[i]^t[i], ...,  p[N]^t[N]).
;;   (4) Finally, reckon the Goedel number G as the product of the N
;;       elements of PS:
;;         G = ps[1]     * ps[2]     * ... * ps[i]     * ... * ps[N]
;;           = p[1]^t[1] * p[2]^t[2] * ... * p[i]^t[i] * ... * p[N]^t[N]
;;       The result constitutes a positive integer number greater than
;;       or equal to 1.
;; 
;; The following sections will provide a more detailed treatise on the
;; aforementioned process of Goedel encoding.
;; 
;; == (0) INVENTORY OF THE WARKLOOMS ==
;; Ere the incipiency of our submergence into the details of the above
;; summarized four-step process, let us iterum review the input data.
;; 
;; We possess a sequence S of plaintext symbols to Goedel-encode into
;; a single integer number, the Godel number G. The sequence S contains
;; a tally of N elements. Our provision further encompasses a mapping E
;; which for each symbol s[i] in S returns a symbol code t[i]. A symbol
;; code uniquely identifies a plaintext symbol by an integer value
;; greater than or equal to 1.
;; 
;; == (1) CONVERT PLAINTEXT SYMBOLS INTO THEIR CODES ==
;; In order to encode a sequence S of plaintext character, tallying N
;; symbols and formulated as
;;   
;;   S = (s[1], s[2], ..., s[i], ...., s[N]),
;; 
;; we first convert each element s[i] into a numeric symbol code t[i].
;; This translation is based upon the encoding table E which associates
;; with each symbol of our alphabet L, and thus with each element of
;; our plaintext sequence S, an integer number greater than or equal
;; to 1. Replacing each symbol s[i] with its symbol code t[i], the new
;; code sequence T is generated:
;;   T = (t[1], t[2], ..., t[i], ..., t[N]),
;; with
;;   t[1] = E(s[1]),
;;   t[1] = E(s[2]),
;;   ...
;;   t[i] = E(s[i]),
;;   ...,
;;   t[N] = E(s[N]).
;; Please remember that the members of T are all integers >= 1.
;; 
;; == (2) PREPARE THE PRIME NUMBERS ==
;; The dependency of the encoding process upon prime numbers manifests
;; in the next stage involving the generation of the first N primes,
;; with N equal to the tally of elements in the input sequence S, or
;; equivalently the cardinality of the symbol codes sequence T. This
;; prime number sequence P, with its elements
;;   P = (p[1], p[2], ..., p[i], ..., p[N])
;; always follows the same pattern, as the prime numbers comprise a
;; fixed set:
;;   P = (2, 3, 5, 7, 11, ...)
;; For instance, the first ten prime numbers (N = 10) enumerate:
;;   P = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29)
;; 
;; == (3) BUILD THE SEQUENCE OF FACTORS ==
;; A Goedel number amounts to a composition of one or more factors,
;; that is, operands in a multiplication; each factor itself constitutes
;; an exponentiation in the form of some prime number p raised to a
;; symbol code t as its exponent, which in conjunction design the term
;; p^t. In this step we determine the factors as a sequence of such
;; exponentiations.
;; 
;; Utilizing the symbol codes sequence T with
;;   T = (t[1], t[2], ..., t[i], ..., t[N]),
;; and the prime sequence P with
;;   P = (p[1], p[2], ..., p[i], ..., p[N]),
;; a new sequence PS is generated by computing at each position i the
;; exponentiation using the prime number p[i] at that position as a base
;; raised to the symbol code t[i] at the same index as an exponent:
;;   PS = (p[1]^t[1], p[2]^t[2], ..., p[i]^t[i], ..., p[N]^t[N])
;;      = (ps[1],     ps[2],     ..., ps[i],     ..., ps[N])
;; 
;; == (4) THE GOEDEL NUMBER: THE PRODUCT OF FACTORS ==
;; Having obtained the sequence of exponentiations PS as
;;   PS = (ps[1],     ps[2],     ..., ps[i],     ..., ps[N])
;;      = (p[1]^t[1], p[2]^t[2], ..., p[i]^t[i], ..., p[N]^t[N]),
;; we now multiply all of its elements into a single number: this
;; already represents the Goedel number --- and thus the Goedel encoding
;; of our plaintext sequence S. The Goedel number G is defined as:
;;   G = ps[1]     * ps[2]     * ... * ps[i]     * ... * ps[N]
;; or, in terms of the explicit exponentiations:
;;   G = p[1]^t[1] * p[2]^t[2] * ... * p[i]^t[i] * ... * p[N]^t[N]
;; This scalar value constitutes an integer greater than or equal to 1.
;; 
;; == THE "GoedelEncode" FUNCTION ==
;; By introduction of a dedicated terminology signifying the Goedel
;; encoding process as a dyadic function "GoedelEncode" accepting two
;; inputs as
;;   (1) the plaintext input sequence S of arbitrary length,
;;   (2) an encoding table E
;;         E: L -> C
;;       mapping to each symbol from the plaintext alphabet L exactly
;;       one symbol code represented by a positive integer number
;;       greater than or equal to 1,
;; and returning the positive integer representing its Goedel number G,
;; we achieve the formulation:
;;   GoedelEncode(S, E) -> G
;; 
;; == EXAMPLE ==
;; Our language L shall be defined as:
;;   
;;   L = { "a", "b", "e", "l", "s", "t", "u" }
;; 
;; An encoding mapping E of the following kind is defined:
;;   
;;   E = { ("a", 1)
;;         ("b", 2)
;;         ("e", 3)
;;         ("l", 4)
;;         ("s", 5)
;;         ("t", 6)
;;         ("u", 7) }
;; 
;; Please remember that, each tuple being one entry, the sinistral
;; constituent represents a plaintext symbol s[i], encoded by its
;; symbol code t[i] in the dextral moeity.
;; 
;; Input:
;;   We want to encode the word "tale", composed of N = 4 symbols:
;;     S = ("t", "a", "l", "e")
;; 
;; Process:
;;   (1) CONVERT PLAINTEXT SYMBOLS INTO THEIR CODES
;;       The plaintext symbol sequence S, being
;;         S = (s[1], s[2], s[3], s[4]),
;;       consisting of N = 4 symbols
;;         s[1] = "t"
;;         s[2] = "a"
;;         s[3] = "l"
;;         s[4] = "e"
;;       must be converted into a sequence T of symbol codes
;;         T = (t[1], t[2], t[3], t[4]).
;;       By avail of the mapping E we obtain:
;;         t[1] = E[s[1]] = E["t"] = 6
;;         t[2] = E[s[2]] = E["a"] = 1
;;         t[3] = E[s[3]] = E["l"] = 4
;;         t[4] = E[s[4]] = E["e"] = 3
;;       This produces the symbol code sequence
;;         T = (s[1], s[2], s[3], s[4])
;;           = (6, 1, 4, 3).
;;   
;;   (2) PREPARE THE PRIME NUMBERS
;;       With the cardinality N of the plaintext sequence S amounting to
;;       N = 4 --- which, by rule of reason, equals the tally of items
;;       in the symbol code sequence T ---, we require the first four
;;       prime numbers as P:
;;         P = (p[1], p[2], p[3], p[4])
;;           = (2,    3,    5,    7).
;;   
;;   (3) BUILD THE SEQUENCE OF FACTORS
;;       The factors of the desired Goedel number are defined by four
;;       elements, given that N = 4. This sequence PS utilizes the
;;       prime sequence P as exponentiation bases:
;;         P = (p[1], p[2], p[3], p[4])
;;           = (2,    3,    5,    7),
;;       and the symbol code sequence T as exponentiation exponents:
;;         T = (t[1], t[2], t[3], t[4])
;;           = (6,    1,    4,    3),
;;       in order to build
;;         PS = (ps[1],     ps[2],     ps[3],     ps[4])
;;            = (p[1]^t[1], p[2]^t[2], p[3]^t[3], p[4]^t[4])
;;            = (   2^6,       3^1,       5^4,       7^3   )
;;            = (    64,         3,       625,       343   )
;;   
;;   (4) THE GOEDEL NUMBER: THE PRODUCT OF FACTORS
;;       Our ultimate objective, the Goedel number G, composes as the
;;       product of the elements in the factor sequence PS, given as
;;         PS = (ps[1], ps[2], ps[3], ps[4])
;;            = (64,        3,   625, 343)
;;       with:
;;         G = ps[1] * ps[2] * ps[3] * ps[4]
;;           = 64    * 3     * 625   * 343
;;           = 41160000
;;       The Goedel number G corresponding to the plaintext symbols
;;       S = "tale", utilizing the encoding map E, thus is:
;;         GodelEncode(("t", "a", "l", "e"), E) = 41160000.
;;                                                ========
;; 
;; 
;; Goedel Decoding
;; ===============
;; The sections following below describe the process for decoding a
;; Goedel number, being a positive integer, with the intention of
;; obtaining its ensconced plaintext symbol sequence S.
;; 
;; == TERMINOLOGY ==
;; The following apercu shall establish a locality for reference if
;; overwhelmed in the face of the symbolic description:
;;   
;;   G  | The Goedel number which shall be decoded to the plaintext
;;      | sequence S.
;;      | It constitutes the product of first N prime numbers P raised
;;      | the power of the symbols codes in T:
;;      |   G = p[1]^t[1] * p[2]^t[2] * ... * p[i]^t[i] * ... * p[N]^t[N]
;;      | The Goedel number is always an integer number greater than or
;;      | equal to 1. The tally N is recovered during the decoding
;;      | process itself.
;;      | By knowledge of G and P we are able to discover T and N, and
;;      | by this ultimately the plaintext symbol sequence S.
;;   ---+---------------------------------------------------------------
;;   C  | The set of possible symbol codes, each mapping to one element
;;      | of the alphabet L. The members of C are exclusively positive
;;      | integer numbers greater than or equal to 1. They enumerate
;;      | as (c[1], c[2], ...).
;;   ---+---------------------------------------------------------------
;;   L  | The alphabet defining the valid symbols. Its elements are
;;      | enumerated as (l[1], l[2], ...).
;;   ---+---------------------------------------------------------------
;;   D  | A mapping which associates with each integer symbol code in
;;      | the set C exactly one plaintext character of the alphabet L.
;;      | The function can be described as:
;;      |   D: C -> L
;;      | When decoding an element c we obtain a plaintext symbol l:
;;      |   D[c] = l, with c in C and l in L.
;;   
;;   N  | The number of elements in the sequence to Goedel-decode.
;;   ---+---------------------------------------------------------------
;;   T  | The sequence of symbol codes to Goedel-decode to the plaintext
;;      | sequence S.
;;      | Each element t[i] must be present in the set of possible
;;      | symbol codes C.
;;      | Each element t[i] encodes the element s[i] from S at the i-th
;;      | position in S, with i in [1, N], according to the mappings
;;      | defined in the decoding table D, that is:
;;      |   t[i] = D[s[i]], with t[i] in T and also t[i] in C.
;;      | Said sequence consists of N members, and thus enumerates as:
;;      |   T = (t[1], t[2], ..., t[i], ..., t[N]), with t[i] in C.
;;   ---+---------------------------------------------------------------
;;   S  | The sequence of plaintext symbols that should be restored from
;;      | the symbol code sequence T by Goedel-decoding.
;;      | Each element s[i] must be present in the alphabet L.
;;      | Logically, the sequence consists of N members, exactly like
;;      | the code sequence T, thus admitted the following formulation:
;;      |    S = (s[1], s[2], ..., s[i], ..., s[N]), with s[i] in L.
;;   ---+---------------------------------------------------------------
;;   P  | The sequence of the first N prime numbers.
;;      | The members are thus enumerated:
;;      |   P = (p[1], p[2], ..., p[i], ... p[N])
;;      | The elements are always equal and follow the pattern
;;      |   P = (2, 3, 5, 7, 11, ...)
;; 
;; == APERCU ==
;; Furnished with the foundational gnarity and the terminological
;; conventions, these appurtenances shall now conjoin into an overview
;; concerning the process of Goedel-decoding.
;; 
;; Given:
;;   - A Goedel number G, being a positive integer greater than or equal
;;     to 1, which is expected to encode a plaintext sequence S.
;;   - An alphabet L encompassing the valid plaintext symbols l[i],
;;     which each element s of S being a member of L.
;;   - A decoding table D which unambiguously maps to each symbol code
;;     c[i], being an integer number greater than or equal to 1, a
;;     plaintext symbol l[i] from the alphabet L. The set of all symbol
;;     codes shall be named C. The mapping is thus formulated:
;;       D: c[i] -> l[i], with c[i] in C and l[i] in L.
;;   - A finite sequence T composed of N symbol codes which can be found
;;     in the set C:
;;       T = (t[1], t[2], ..., t[i], ..., t[N]), with t[i] in C.
;; 
;; Task:
;;   - The Goedel number G, a positive integer number greater than or
;;     equal to 1, shall be decoded, that is, mapped to a sequence S of
;;     plaintext symbols.
;; 
;; Process:
;;   (1) The symbol codes composing T, defined as
;;         T = (t[1], t[2], ..., t[i], ..., t[N])
;;       and, as a concomitant thereof, their tally N, which also equals
;;       the cardinality of the desired plaintext symbol sequence S,
;;       must be retrieved. To do so, iterate over the prime numbers P
;;         P = (2, 3, 5, 7, 11, ...),
;;       counting for every member p[i] the number of its complete
;;       occurrences in the Goedel number G; thus every p[i] produces
;;       a nonnegative integer which is already the value of the symbol
;;       code t[i] at the position of i of the prime p[i] in the prime
;;       sequence P. The first such count t[i] that produces the value
;;       zero (0) ends this process. The result of applying the first N
;;       prime numbers p[i], where N is tantamount to the tally of
;;       primes not having produced a t[i] of zero, generates the
;;       symbol code sequence T:
;;         T = (t[1], t[2], ..., t[i], ..., t[N]).
;;       The function used to compute the number of occurrences of a
;;       prime number p[i], or equivalently the symbol code t[i], in the
;;       Goedel number G can be described in the following pseudocode:
;;         function getSymbolCode (G, p[i])
;;           let symbolCode <- 0
;;           let quotient   <- G
;;           while (quotient modulo p[i]) = 0
;;             symbolCode <- symbolCode + 1
;;             quotient   <- quotient / 2
;;           end while
;;           return symbolCode
;;         end function
;;   (2) Calculate for the symbol code sequence T
;;         T = (t[1], t[2], ..., t[i], ..., t[N])
;;       the plaintext symbol sequence S
;;         S = (s[1], s[2], ..., s[i], ..., s[N])
;;       by substituting each symbol code t[i] by the symbol s[i] using
;;       the decoding mapping D:
;;         s[i] = D(t[i])
;;       The resulting sequence S already constitutes our desideratum.
;; 
;; == (0) INVENTORY OF THE WARKLOOMS ==
;; Ere the incipiency of the submergence into the details of our above
;; summarized four-step process, let us iterum review the input data.
;; 
;; We possess a Goedel number G, being an integer number greater than or
;; equal to 1. This value, as any positive integer, can be constructed
;; by the unique product of one or more prime numbers --- the
;; fundamental theorem of arithmetic.
;; 
;; In addition, a mapping D is provided, assigning to each symbol code
;; t[i], itself an integer number not less than 1, a plaintext symbol
;; s[i], thus uniquely resolving to such a destination datum. Finally,
;; we are cognizant that the prime numbers P constitute an infinite
;; sequence, designated with p[1], p[2], etc., and starting with
;; 2, 3, 5, 7, 11, etc.
;; 
;; == (1) EXTRACT THE SYMBOL CODES FROM THE GOEDEL NUMBER ==
;; Given a Goedel number G, the inicipient step involves the extraction
;; of the encoded symbol codes T, with
;;   T = (t[1], t[2], ..., t[i], ..., t[N])
;; for a yet unknown tally of codes, equal also to the cardinality of
;; the ultimately resulting plaintext symbol sequence S.
;; 
;; The extraction process is realized by adminicle of the prime numbers
;;   P = (2, 3, 5, 7, 11, ...).
;; A Goedel number being expressed as the production of the first N
;; prime numbers, each raised to an integer exponent not less than 1,
;; with any not included prime number practically contained, but raised
;; to the power 0 which renders it the neutral element 1 (= base^0 = 1),
;; the exponent actually determines how many times a prime number is
;; included in the Goedel number --- these exponents, however, are
;; paravaunt already the symbol codes t[1], t[2], ..., t[i], ..., t[N],
;; ordered by the association with the i-th prime number.
;; 
;; This gnarity equipping us, we ought to determine
;;   (a) The prime numbers contained in the Goedel number G, obtained in
;;       their natural order in P, meaning:
;;         P = (2, 3, 5, 7, 11, ...)
;;   (b) The exponent of each contained prime number, that is, the
;;       symbol code encoded at the i-th position, with i being the
;;       index of the respective prime number p[i] in P.
;; 
;; Given a prime number p[i], the tally of its occurrences in the Goedel
;; number G can be discovered through repeated division of G by p[i],
;; each time substituting G by the operation's quotient, until aN odd
;; remainder (= current G modulo p[i]) issues. The count of divisions
;; without rest preceding this event constitutes the exponent, that is,
;; the tally of occurrences of p[i] in G --- and this number also
;; describes the symbol code at the i-th position of the symbol code
;; sequence T. A very simplistic exposition of this process might be
;; limned in the following:
;;   
;;   let symbolCode <- 0
;;   
;;   if (G modulo p[i]) = 0 then
;;     increase symbolCode by one
;;     G <- G / p[i]
;;   else
;;     end process
;;   end If
;;   
;;   return symbolCode
;; 
;; In order to furnish a referrable unit, we ensconce the just
;; explicated process, concomitantly stressing the necessity to not
;; modify the original Goedel number G by its application. --- This
;; manifests more as a tenet of programmatical contemplation, as the
;; mathematical concept of variables proscribes their modification,
;; while computer science oftentimes embraces such surgery. The
;; resulting function entity shall be agnominated "getSymbolCode", and
;; as its inputs it shall admit the Goedel number G to analyze and the
;; prime number p[i] whose tally is to be counted. It returns as its
;; sole result this exact integer number greater than or equal to zero
;; which, if amounting to at least 1, represents the symbol code at the
;; i-th position in the symbol code sequence T. The sentinel value 0
;; designates the prime number p[i]'s lacuna in G, thus signifying that
;; the position i lies beyond the cardinality of T.
;;   
;;   function getSymbolCode (G, p[i])
;;     { The symbol code t[i] at the position p[i].                  }
;;     { Being an nonnegative integer, it constitutes the exponent   }
;;     { to which p[i] was raised when encoding the Goedel number G. }
;;     let symbolCode <- 0
;;     let quotient   <- G
;;     
;;     { Examine how many complete times p[i] is contained in G;     }
;;     { this number equals the symbolCode t[i].                     }
;;     while (quotient modulo p[i]) = 0
;;       symbolCode <- symbolCode + 1
;;       quotient   <- quotient / p[i]
;;     end while
;;     
;;     return symbolCode
;;   end function
;; 
;; If we apply the prime numbers contained in P in their natural order,
;; p[1], p[2], etc., the symbol codes of T --- t[1], t[2], ... --- will
;; be restored in their exact order and number. The first p[i] for the
;; same getSymbolCode(G, p[i]) produces a zero value signifies the
;; perfection of the symbol codes sequence T, such that no further
;; indagation is necessitated. Concretely, we adhere to this approach:
;;   
;;   function getSymbolCodes (G)
;;     { The symbol code sequence T is yet empty. }
;;     let T <- ()
;;     
;;     { Iterate over the prime numbers in P in the correct order. }
;;     for p[i] in P
;;       let t[i] <- getSymbolCode(G, p[i])
;;       
;;       { A symbol code t[i] (or exponent to which p[i] is raised) }
;;       { which equals zero betokens a prime number p[i] not being }
;;       { contained in the Goedel number G at all. As a Goedel     }
;;       { number uses the prime numbers  p[1], p[2], etc. in their }
;;       { correct order, a t[i] designates that the corresponding  }
;;       { prime p[i], and thus every following prime number        }
;;       { p[i+1], p[i+2], etc., is contained contained in G.       }
;;       if t[i] != 0 then
;;          append t[i] to T
;;       else
;;          end the process
;;       end if
;;     end for
;;     
;;     return T
;;   end function
;; 
;; == (2) CONVERT THE SYMBOL CODES INTO PLAINTEXT SYMBOLS ==
;; The discovery of the N symbol codes t[1] to t[N] which comprise the
;; symbol code sequence T as
;;   T = (t[1], t[2], ..., t[i], ..., t[N])
;; has endowed us with sufficient cognizance to decode the source
;; Goedel number G into its plaintext constituents. Given the decoding
;; mapping D, that produces for a symbol code t[i] the plaintext symbol
;; s[i], we substitute each symbol code t[i] by its plaintext symbol
;; s[i], with
;;   s[1] = D(t[1]),
;;   s[2] = D(t[2]),
;;   ...,
;;   s[i] = D(t[i]),
;;   ...,
;;   s[N] = D(t[N]).
;; thus restoring the original symbol sequence S as
;;   S = (s[1], s[2], ..., s[i], ...., s[N]).
;; 
;; == THE "GoedelDecode" FUNCTION ==
;; By introduction of a dedicated terminology signifying the Goedel
;; decoding process as a dyadic function "GoedelDecode" accepting two
;; inputs:
;;   (1) the Goedel number G as an integer greater than or equal to 1,
;;   (2) a decoding table D
;;         D: C -> L
;;       mapping to each symbol code c, represented by a positive
;;       integer number greater than or equal to 1, exactly one
;;       plaintext symbol of the alphabet L, 
;; and returning as its sole result the decoded plaintext sequence S,
;; we achieve the following forumulation:
;;   GoedelDecode(G, D) -> S
;; 
;; == EXAMPLE ==
;; Our language L shall be defined as:
;;   
;;   L = { "a", "b", "e", "l", "s", "t", "u" }
;; 
;; An decoding mapping D of the following kind is defined:
;;   
;;   D = { (1, "a")
;;         (2, "b")
;;         (3, "e")
;;         (4, "l")
;;         (5, "s")
;;         (6, "t")
;;         (7, "u") }
;; 
;; Please remember that, each tuple being one entry, the sinistral
;; constituent represents a symbol code t[i], encoding the symbol s[i]
;; present in the dextral moeity.
;; 
;; Input:
;;   We want to decode Goedel number G with
;;     G = 41160000
;;   into its plaintext symbols
;;     S = (s[1], s[2], ..., s[i], ..., s[N]).
;; 
;; Process:
;;   (1) EXTRACT THE SYMBOL CODES FROM THE GOEDEL NUMBER
;;       In order to reproduce the symbol code sequence
;;         T = (t[1], t[2], ..., t[i], ..., t[N]),
;;       utilized during the encoding of the plaintext symbols S as
;;         S = (s[1], s[2], ..., s[i], ..., s[N]),
;;       which originally produces the Goedel number G as
;;         G = 41160000,
;;       we require the aid of the prime numbers in their correct order,
;;       denominated by
;;         P = (p[1], p[2], ..., p[i], ...)
;;       
;;       Each prime number p[i] is divided into G to obtain the
;;       nonnegative integer exponent t[i] --- the symbol code ---
;;       which, by yielding p[i]^t[i], availed in creating G. This
;;       process being applied to the primes p[1], p[2], ..., until one
;;       of these inputs produces an exponent t[i] of zero, designating
;;       the exhaustion of our search for the symbol codes in T.
;;       
;;       We perform the first and final division operations manually in
;;       order to explore the basic concepts:
;;       
;;       (i) The first prime number p[1] = 2:
;;             t[1]     = 0
;;             quotient = G = 41160000
;;             
;;             (a) remainder = quotient modulo 2
;;                           = 41160000 modulo 2
;;                           = 0
;;                 
;;                 The remainder equals 0, thus:
;;                 quotient = quotient / 2
;;                          = 41160000 / 2 = 41160000
;;                          = 20580000
;;                 
;;                 t[1] = t[1] + 1
;;                      = 0 + 1
;;                      = 1
;;             
;;             (b) remainder = quotient modulo 2
;;                           = 20580000 modulo 2
;;                           = 0
;;                 
;;                 The remainder equals 0, thus:
;;                 quotient = quotient / 2
;;                          = 20580000 / 2 = 10290000
;;                          = 10290000
;;                 
;;                 t[1] = t[1] + 1
;;                      = 1 + 1
;;                      = 2
;;             
;;             (c) remainder = 10290000 mod 2 = 0
;;                 quotient  = 10290000 /   2 = 5145000
;;                 t[1]      = 3
;;             
;;             (d) remainder = 5145000 mod 2 = 0
;;                 quotient  = 5145000 /   2 = 2572500
;;                 t[1]      = 4
;;             
;;             (d) remainder = 2572500 mod 2 = 0
;;                 quotient  = 2572500 /   2 = 1286250
;;                 t[1]      = 5
;;             
;;             (e) remainder = 1286250 mod 2 = 0
;;                 quotient  = 1286250 /   2 = 643125
;;                 t[1]      = 6
;;             
;;             (f) remainder = 643125 mod 2 = 1
;;                 The remainder does not equal zero.
;;                 => Thus, terminate process.
;;           
;;           Result: t[1] = 6.
;;           This means that the first prime numer p[1] = 2 has been
;;           multiplied by itself 6 times, p[1]^t[1] = 2^6, in order to
;;           yield the Goedel number G = 41160000.
;;           This also means that the first plaintext symbol s[1] has
;;           been encoded by the symbol code 6.
;;       
;;       (ii)  p[2] = 3
;;             => t[2] = 1
;;       
;;       (iii) p[3] = 5
;;             => t[3] = 4
;;       
;;       (iv)  p[4] = 7
;;             => t[4] = 3
;;             
;;       (v)   p[5] = 11
;;               t[5]     = 0
;;               quotient = G = 41160000
;;             
;;               (a) remainder = quotient modulo 11
;;                             = 41160000 modulo 11
;;                             = 2
;;                 
;;                   The remainder does not equal zero.
;;                   Thus, do not collect t[5]; instead, terminate the
;;                   complete search process.
;;                   As t[5] = 0, this prime number 11 constitutes the
;;                   first prime number not contained in G.
;;                   => This and any subsequent prime number from P are
;;                      not part of the encoding of G.
;;                   => All symbol codes in T have been discovered:
;;                        T = (t[1], t[2], t[3], t[4])
;;                          = (6,    1,    4,    3)
;;                   => The number of symbol codes N equals 4:
;;                        N = 4.
;;                      This equals also the number of plaintext symbols
;;                      in S:
;;                        S = (s[1], s[2], ..., s[i], ..., s[N])
;;                          = (s[1], s[2], s[3], s[4])
;;   
;;   (2) CONVERT THE SYMBOL CODES INTO PLAINTEXT SYMBOLS
;;       The recognition of the symbol sequence T and its cardinality
;;       N = 4 as
;;         T = (t[1], t[2], t[3], t[4])
;;       endows us with the capacitation to discover the plaintext
;;       sequence S, naturally composed of N = 4 elements:
;;         S = (s[1], s[2], s[3], s[4]).
;;       The key for the conversion wones in the decoding table D, with
;;         D = { (1, "a")
;;               (2, "b")
;;               (3, "e")
;;               (4, "l")
;;               (5, "s")
;;               (6, "t")
;;               (7, "u") }.
;;       By avail of the mapping D we obtain:
;;         s[1] = D[t[1]] = D[6] = "t"
;;         s[2] = D[t[2]] = D[1] = "a"
;;         s[3] = D[t[3]] = D[4] = "l"
;;         s[4] = D[t[4]] = D[3] = "e"
;;       This produces the symbol code sequence
;;         S = (s[1], s[2], s[3], s[4])
;;           = ("t",  "a",  "l",  "e").
;;       
;;       The plaintext symbol sequence S corresponding to the Goedel
;;       number G thus is:
;;         GoedelDecode(41160000, D) = ("t", "a", "l", "e").
;;                                     ====================
;; 
;; --------------------------------------------------------------------
;; 
;; Author: Kaveh Yousefi
;; Date:   2022-02-15
;; 
;; Sources:
;;   [esolang2021goedelang]
;;   -> "https://esolangs.org/wiki/G%C3%B6delang"
;;       o Specification of the esoteric programming language
;;         "GÃ¶delang", a "brainfuck" derivative based upon GÃ¶del numbers.
;;   
;;   [meyer2021goedel3]
;;   -> "https://www.jamesrmeyer.com/ffgit/GodelSimplified3.html"
;;       o Main page: "https://www.jamesrmeyer.com/ffgit/GodelSimplified0.html"
;;       o Describes Goedel numbers in a pellucid manner.
;;       o Provides an example.
;;   
;;   [panu20022sepgoedelincompleteness]
;;   -> "https://plato.stanford.edu/entries/goedel-incompleteness/sup1.html"
;;   
;;   [rod2018factoringinalgebra]
;;   -> "https://www.mathsisfun.com/algebra/factoring.html"
;;       o Describes factorization.
;;   
;;   [rod2021fundtheoremofarithm]
;;   -> "https://www.mathsisfun.com/numbers/fundamental-theorem-arithmetic.html"
;;       o Describes the Fundamental Theorem of Arithmetic in simple
;;         terms.
;;       o The theorem states that:
;;           "Any integer greater than 1 is either a prime number, or
;;            can be written as a unique product of prime numbers
;;            (ignoring the order)."
;;   
;;   [rod2021primefactorization]
;;   -> "https://www.mathsisfun.com/prime-factorization.html"
;;       o Describes prime numbers and prime factorization in simple
;;         terms.
;;   
;;   [wikiwikiweb2005goedelnumbering]
;;   -> "https://wiki.c2.com/?GoedelNumbering"
;;   
;;   [wikipedia2021goedelnumbering]
;;   -> "https://en.wikipedia.org/wiki/G%C3%B6del_numbering"
;; 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; -- Declaration of types.                                        -- ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(deftype prime-generator ()
  "The ``prime-generator'' type defines a niladic function which,
   starting with the value two (2), upon each invocation returns the
   next prime number."
  '(function () (integer 2 *)))

;;; -------------------------------------------------------

(deftype list-of (&optional (element-type T))
  "The ``list-of'' type defines a list of zero or more elements, each
   of which conforms to the ELEMENT-TYPE, the same defaults to the
   comprehensive ``T''."
  (let ((predicate (gensym)))
    (declare (type symbol predicate))
    (setf (symbol-function predicate)
      #'(lambda (object)
          (declare (type T object))
          (and
            (listp object)
            (every
              #'(lambda (element)
                  (declare (type T element))
                  (typep element element-type))
              (the list object)))))
    `(satisfies ,predicate)))

;;; -------------------------------------------------------

(deftype hash-table-of (&optional (key-type T) (value-type T))
  "The ``hash-table-of'' type defines a hash table of zero or more
   entries, each key of which conforms to the KEY-TYPE, asssociated with
   a value of the VALUE-TYPE, both defaulting to the
   comprehensive ``T''."
  (let ((predicate (gensym)))
    (declare (type symbol predicate))
    (setf (symbol-function predicate)
      #'(lambda (object)
          (declare (type T object))
          (and
            (hash-table-p object)
            (loop
              for key
                of-type T
                being the hash-keys in (the hash-table object)
              using
                (hash-value value)
              always
                (and (typep key   key-type)
                     (typep value value-type))))))
    `(satisfies ,predicate)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; -- Prime number generator.                                      -- ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun prime-p (candidate)
  "Checks whether the CANDIDATE integer represents a prime number,
   returning on confirmation a ``boolean'' value of ``T'', otherwise
   ``NIL''."
  (declare (type (integer 2 *) candidate))
  (the boolean
    (loop
      for divisor
        of-type (integer 1 *)
        from    candidate
        downto  2
      when (zerop (mod candidate divisor))
        count 1 into number-of-divisors
      when (>= number-of-divisors 2)
        do (return NIL)
      finally
        (return T))))

;;; -------------------------------------------------------

(defun make-prime-generator ()
  "Creates and returns a niladic function which, starting with the value
   two (2), returns upon each invocation the next prime number.
   ---
   Example:
     ;; Print the first ten prime numbers to the standard output, that
     ;; is: 2, 3, 5, 7, 11, 13, 17, 19, 23, 29.
     (let ((generator (make-prime-generator)))
       (declare (type (function () (integer 2 *)) generator))
       (loop repeat 10 do
         (print (funcall generator))))"
  (let ((next-prime 2))
    (declare (type (integer 2 *) next-prime))
    (the function
      #'(lambda ()
          (the (integer 2 *)
            (prog1 next-prime
              (loop
                do    (incf next-prime)
                until (prime-p next-prime))))))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; -- Goedel number encoder.                                       -- ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun compute-symbol-codes (source encoding-table)
  "Returns a list containing the positive integer symbol codes produced
   by encoding the plaintext SOURCE using the ENCODING-TABLE.
   ---
   Given a sequence of N = 4 number of SOURCE elements
     S = (s1, s2, ..., si, ...., sN),
   and an ENCODING-TABLE operating as a mapping E from a SOURCE element
   ai to a non-negative integer symbol code ti
     E: li -> ci, with li in L and ci as an integer >= 0,
   a sequence of symbol codes T is produced:
     T = (t1, t2, ..., ti, ..., tN).
   The first N prime numbers
     P = (p1, p2, ..., pi, ..., pN)
   will be generated. Each prime number bi is then taken to the power
   of the respective symbol code ti to yield an exponentiation result
     ps[i] = pi^{ti}.
   The product G of these N powers ps[i] constitutes the resulting
   Goedel number
     G = (p1^{t1}) * (p2^{t2}) * ... * (pi^{ti}) * ... * (pN^{tN})
       =  ps[1]    *  ps[2]    * ... *  ps[i]    * ... *  ps[N].
   By doing so, the symbol code sequence T is Goedel-encoded.
   ---
   Granted as an example of this process, we are presented with a SOURCE
     S = ( 't', 'a', 'l', 'e' )
   and an ENCODING-TABLE
     E: li -> ci
   with the definitions
     E = { 'a' -> 1,
           'b' -> 2,
           'e' -> 3,
           'l' -> 4,
           's' -> 5
           't' -> 6
           'u' -> 7 },
   mapping to a plaintext symbol li from the alphabet L a positive
   integer symbol code ci, and defined by the entries
     e1 = (l1 -> c1) = ('a' -> 1)
     e2 = (l2 -> c2) = ('b' -> 2)
     e3 = (l3 -> c3) = ('e' -> 3)
     e4 = (l4 -> c4) = ('l' -> 4)
     e5 = (l5 -> c5) = ('s' -> 5)
     e6 = (l6 -> c6) = ('t' -> 6)
     e7 = (l7 -> c7) = ('u' -> 7)
   or in a tabular guise:
     Symbol (li) | Code (ci)
     ------------+------------
          a      |  1
          b      |  2
          e      |  3
          l      |  4
          s      |  5
          t      |  6
          u      |  7
   The symbol sequence matching the five elements of A encompasses
     T = (6, 1, 4, 3).
   The first N = 4 prime numbers enumerate as follows:
     P = (2, 3, 5, 7).
   The product of the powers, which is tantamount to the Goedel number,
   resolves to:
     G = (2^6 * 3^1 *   5^4 *     7^3)
       =   16 * 729 * 78125 * 5764801
       =   64 *   3 *   625 * 343
       = 41160000.
   In corollary, the SOURCE sequence
     S = ( 't', 'a', 'l', 'e' )
   is mapped to the symbol sequence
     T = (6, 1, 4, 3),
   which is finally Goedel-encoded as
     G = 41160000,
   that is:
     GoedelEncode(('t', 'a', 'l', 'e'), E) = 41160000."
  (declare (type sequence                        source))
  (declare (type (hash-table-of T (integer 0 *)) encoding-table))
  (the (list-of (integer 1 *))
    (map 'list
      #'(lambda (symbol)
          (declare (type T symbol))
          (multiple-value-bind (symbol-code contains-symbol)
              (gethash symbol encoding-table)
            (declare (type (or null (integer 0 *)) symbol-code))
            (declare (type T                       contains-symbol))
            (when contains-symbol
              (the (integer 0 *) symbol-code))))
      source)))

;;; -------------------------------------------------------

(defun compute-goedel-number (symbol-codes)
  "Encodes the list of non-negative integer SYMBOL-CODES as a
   Goedel number and returns the same.
   ---
   Given a sequence of input symbol codes
     T = (t1, t2, ..., ti, ..., tN),
   The first N prime numbers
     P = (p1, p2, ..., pi, ..., pN)
   will be generated. Each prime number pi is then taken to the power
   of the respective symbol code ti to yield an exponentiation result
     ps[i] = pi^{ti}.
   The product G of these N powers ps[i] constitutes the resulting
   Goedel number
     G = ps[1]     * ps[2]     * ... * ps[i]     * ... * ps[N]
       = (p1^{t1}) * (p2^{t2}) * ... * (pi^{ti}) * ... * (pN^{tN}).
   By doing so, the symbol code sequence T is Goedel-encoded.
   ---
   Granted as an example of this process, we are presented with an input
   symbol sequence of five elements, that is, N = 4, which encompasses
     T = (6, 1, 4, 3).
   The first N = 4 prime numbers enumerate as follows:
     P = (2, 3, 5, 7).
   The product of the powers, which is tantamount to the Goedel number,
   resolves to:
     G = (2^6 * 3^1 *   5^4 *     7^3)
       =   16 * 729 * 78125 * 5764801
       =   64 *   3 *   625 * 343
       = 41160000
   In corollary, the symbol sequence T = (6, 1, 4, 3) is
   Goedel-encoded as 41160000, that is:
     computeGoedelNumber((6, 1, 4, 3)) = 41160000."
  (declare (type (list-of (integer 0 *)) symbol-codes))
  (let ((prime-generator (make-prime-generator)))
    (declare (type prime-generator prime-generator))
    (the (integer 0 *)
      (reduce
        #'(lambda (accumulator code)
            (declare (type (integer 0 *) code))
            (let ((prime (funcall prime-generator)))
              (declare (type (integer 2 *) prime))
              (the (integer 2 *) (* accumulator (expt prime code)))))
        symbol-codes
        :initial-value 1))))

;;; -------------------------------------------------------

(defun goedel-encode (source encoding-table)
  "Encodes the SOURCE sequence as a Goedel number using the
   ENCODING-TABLE as the mapping from each SOURCE element to an
   identifying non-negative integer symbol code, and returns the
   Goedel number matching the encoded SOURCE.
   ---
   Given a sequence of N = 4 number of SOURCE elements
     S = (s1, s2, ..., si, ...., sN),
   and an ENCODING-TABLE operating as a mapping E from a SOURCE element
   ai to a non-negative integer symbol code ti
     E: li -> ci, with li in L and ci as an integer >= 0,
   a sequence of symbol codes T is produced:
     T = (t1, t2, ..., ti, ..., tN).
   The first N prime numbers
     P = (p1, p2, ..., pi, ..., pN)
   will be generated. Each prime number bi is then taken to the power
   of the respective symbol code ti to yield an exponentiation result
     ps[i] = pi^{ti}.
   The product G of these N powers ps[i] constitutes the resulting
   Goedel number
     G = (p1^{t1}) * (p2^{t2}) * ... * (pi^{ti}) * ... * (pN^{tN})
       =  ps[1]    *  ps[2]    * ... *  ps[i]    * ... *  ps[N].
   By doing so, the symbol code sequence T is Goedel-encoded.
   ---
   Granted as an example of this process, we are presented with a SOURCE
     S = ( 't', 'a', 'l', 'e' )
   and an ENCODING-TABLE
     E: li -> ci
   with the definitions
     E = { 'a' -> 1,
           'b' -> 2,
           'e' -> 3,
           'l' -> 4,
           's' -> 5
           't' -> 6
           'u' -> 7 },
   mapping to a plaintext symbol li from the alphabet L a positive
   integer symbol code ci, and defined by the entries
     e1 = (l1 -> c1) = ('a' -> 1)
     e2 = (l2 -> c2) = ('b' -> 2)
     e3 = (l3 -> c3) = ('e' -> 3)
     e4 = (l4 -> c4) = ('l' -> 4)
     e5 = (l5 -> c5) = ('s' -> 5)
     e6 = (l6 -> c6) = ('t' -> 6)
     e7 = (l7 -> c7) = ('u' -> 7)
   or in a tabular guise:
     Symbol (li) | Code (ci)
     ------------+------------
          a      |  1
          b      |  2
          e      |  3
          l      |  4
          s      |  5
          t      |  6
          u      |  7
   The symbol sequence matching the five elements of A encompasses
     T = (6, 1, 4, 3).
   The first N = 4 prime numbers enumerate as follows:
     P = (2, 3, 5, 7).
   The product of the powers, which is tantamount to the Goedel number,
   resolves to:
     G = (2^6 * 3^1 *   5^4 *     7^3)
       =   16 * 729 * 78125 * 5764801
       =   64 *   3 *   625 * 343
       = 41160000.
   In corollary, the SOURCE sequence
     S = ( 't', 'a', 'l', 'e' )
   is mapped to the symbol sequence
     T = (6, 1, 4, 3),
   which is finally Goedel-encoded as
     G = 41160000,
   that is:
     GoedelEncode(('t', 'a', 'l', 'e'), E) = 41160000."
  (declare (type sequence                        source))
  (declare (type (hash-table-of T (integer 0 *)) encoding-table))
  (the (integer 0 *)
    (compute-goedel-number
      (compute-symbol-codes source encoding-table))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; -- Goedel number decoder.                                       -- ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun extract-symbol-code (goedel-number base)
  "Returns the symbol code associated with the prime number BASE as a
   factor of the GOEDEL-NUMBER.
   ---
   This function effectively computes and delivers the exponent to the
   BASE in the GOEDEL-NUMBER, which is equivalent to the number of times
   the BASE was multiplied by itself while generating the GOEDEL-NUMBER.
   ---
   The BASE should be a prime number, according in this to the
   foundation of the Goedel number generation.
   ---
   Emanating from a mathematical conspectuity, the returned exponent
   includes in the compass of its interpretation a second, actually
   paravaunt, signification, which justifies the function's
   agnomination: It is tantamount to the symbol code located at the
   position of the prime BASE. If, for instance, we calculate
     (extract-symbol-code 41160000 7)
   obtaining as the result the number
     3,
   we learn that, with the BASE 7 being the *FOURTH* prime number, the
   symbol code 3, associated with some context-specific plaintext
   symbol, is located at the *FOURTH* position of the Goedel-encoded
   source.
   ---
   Example:
     (extract-symbol-code 41160000 2)
     => Returns 6. This means that the number 2 was multiplied by itself
        six times (= 2 * 2 * 2 * 2 * 2 * 2 = 2^6) as a factor to create
        the Goedel number 41160000.
   ---
   If perusing the source code of this function, please heed that the
   division is implemented in terms of ``floor'' rather than ``round'',
   as the former vouches for a non-negative remainder, whereas the
   latter may produce any species of integer, including a negative
   datum --- a fact that might confound potential maintainers."
  (declare (type (integer 2 *) goedel-number))
  (declare (type (integer 2 *) base))
  (let ((quotient  goedel-number)
        (remainder 0))
    (declare (type (integer 0 *) quotient))
    (declare (type (integer 0 *) remainder))
    (the (integer 0 *)
      (loop
        do    (multiple-value-setq (quotient remainder)
                (floor quotient base))
        while (zerop remainder)
        count 1))))

;;; -------------------------------------------------------

(defun extract-symbol-codes (goedel-number)
  "Returns a list containing the original numeric sequence of symbol
   codes used to build the GOEDEL-NUMBER.
   ---
   Example:
     (extract-symbol-codes 41160000)
     => Returns (6 1 4 3). This means that the first four prime
        numbers 2, 3, 5, 7 were raised as bases to the respectively
        located symbol codes, as exponents, in order to obtain the
        Goedel number 41160000:
          
          Symbol codes  | 6   | 1   | 4   | 3
          .....................................
          Prime numbers | 2   | 3   | 5   | 7 
          Powers        | 2^6 | 3^1 | 5^4 | 7^3
          Factors       | 64  | 3   | 625 | 343
          Product       | 64  * 3   * 625 * 343
          =====================================
          Goedel number | 41160000"
  (declare (type (integer 2 *) goedel-number))
  (let ((prime-generator (make-prime-generator)))
    (declare (type prime-generator prime-generator))
    (the (list-of (integer 0 *))
      (loop
        for base
          of-type (integer 2 *)
          =       (funcall prime-generator)
        for exponent
          of-type (integer 0 *)
          =       (extract-symbol-code goedel-number base)
        while   (plusp exponent)
        collect exponent))))

;;; -------------------------------------------------------

(defun goedel-decode (goedel-number decoding-table)
  "Extracts from the GOEDEL-NUMBER the plaintext source symbols in a
   list, using the DECODING-TABLE as the mapping from each symbol code,
   represented by a prime number's positive integer exponent, to the
   plaintext symbol.
   ---
   Given a Goedel number G with
     G = 41160000
   and a DECODING-TABLE
     D: ci -> li
   mapping to a positive integer symbol code ci an arbitrary plaintext
   source symbol li, and defined by the entries
     d1 = (c1 -> l1) = (1 -> 'a')
     d2 = (c2 -> l2) = (2 -> 'b')
     d3 = (c3 -> l3) = (2 -> 'e')
     d4 = (c4 -> l4) = (4 -> 'l')
     d5 = (c5 -> l5) = (5 -> 's')
     d6 = (c6 -> l6) = (6 -> 't')
     d7 = (c7 -> l7) = (5 -> 'u')
   or in a tabular guise:
     Code (ci) | Symbol (li)
     ----------+------------
          1    |  a
          2    |  b
          3    |  e
          4    |  l
          5    |  s
          6    |  t
          7    |  u
   the Goedel number G is in a first step reduced to the exponents of
   the first N prime numbers P:
     P = (2, 3, 5, 7).
   With N being the number of non-zero exponents calculated in the
   process, and equal to N = 4 in this case. These computed exponents
   encompass the sequence of positive integer numbers greater than zero
   called T:
     T = (6, 1, 4, 3),
   or in a more explicit form:
     t[1] = 6
     t[2] = 1
     t[3] = 4
     t[4] = 3,
   where each exponent ti represents a symbol code, expected to be
   found as a key of the DECODING-TABLE. This means that any element ti
   is a subset of C = {c1, ..., ci, ...cM}, for
     M = number of entries di in the DECODING-TABLE D.
   In the last step, the symbol codes ti are substituted by the
   corresponding plaintext symbols, as defined by the DECODING-TABLE
   mapping (ci -> li), yielding the result plaintext sequence
     S = (s1, s2, s3, s4),
   where
     s[1] = D[t[1]] = D[6] = 't'
     s[2] = D[t[2]] = D[1] = 'a'
     s[3] = D[t[3]] = D[4] = 'l'
     s[3] = D[t[4]] = D[3] = 'e',
   which ultimately manifests in
     S = ('t', 'a', 'l', 'e')
   ---
   In corollary, the Goedel number
     G = 41160000
   is resolved into its symbol codes (or prime number exponents)
     T = (6, 1, 4, 3),
   which are then mapped to the sequence of plaintext symbol
     S = ( 't', 'a', 'l', 'e')
   by mediation of the code-to-symbol decoding table
     D = {(1 -> 'a'),
          (2 -> 'b'),
          (3 -> 'e'),
          (4 -> 'l'),
          (5 -> 's'),
          (6 -> 't'),
          (7 -> 'u')}
   as a result of the function
     GoedelDecode(41160000, D) = ( 't', 'a', 'l', 'e')."
  (declare (type (integer 2 *)                   goedel-number))
  (declare (type (hash-table-of (integer 0 *) T) decoding-table))
  (let ((symbol-codes (extract-symbol-codes goedel-number)))
    (declare (type (list-of (integer 0 *)) symbol-codes))
    (the (list-of T)
      (mapcar
        #'(lambda (symbol-code)
            (declare (type (integer 0 *) symbol-code))
            (the T (gethash symbol-code decoding-table)))
        symbol-codes))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; -- Example 01: Encoding.                                        -- ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Goedel-encoding of the example in the header documentation.
;; 
;; Our language L shall be defined as:
;;   
;;   L = { "a", "b", "e", "l", "s", "t", "u" }
;; 
;; An encoding mapping E of the following kind is defined:
;;   
;;   E = { ("a", 1)
;;         ("b", 2)
;;         ("e", 3)
;;         ("l", 4)
;;         ("s", 5)
;;         ("t", 6)
;;         ("u", 7) }
;; 
;; Input:
;;   S = ("t", "a", "l", "e")
;; 
(let ((encoding-table (make-hash-table :test #'eql)))
  (declare (type (hash-table-of character (integer 1 *)) encoding-table))
  (setf (gethash #\a encoding-table) 1)
  (setf (gethash #\b encoding-table) 2)
  (setf (gethash #\e encoding-table) 3)
  (setf (gethash #\l encoding-table) 4)
  (setf (gethash #\s encoding-table) 5)
  (setf (gethash #\t encoding-table) 6)
  (setf (gethash #\u encoding-table) 7)
  
  (let ((plaintext-sequence "tale"))
    (declare (type string plaintext-sequence))
    
    (let ((encoded-sequence
            (compute-symbol-codes plaintext-sequence encoding-table))
          (goedel-number
            (goedel-encode plaintext-sequence encoding-table)))
      (declare (type (list-of (integer 1 *)) encoded-sequence))
      (declare (type (integer 0 *)           goedel-number))
      
      (format T "~&S = ~s" plaintext-sequence)
      (format T "~&T = ~s" encoded-sequence)
      (format T "~&G = ~s" goedel-number))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; -- Example 02: Decoding.                                        -- ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Goedel-decoding of the example in the header documentation.
;; 
;; Our language L shall be defined as:
;;   
;;   L = { "a", "b", "e", "l", "s", "t", "u" }
;; 
;; An decoding mapping D of the following kind is defined:
;;   
;;   D = { (1, "a")
;;         (2, "b")
;;         (3, "e")
;;         (4, "l")
;;         (5, "s")
;;         (6, "t")
;;         (7, "u") }
;; 
;; Input:
;;   G = 41160000
;; 
(let ((decoding-table (make-hash-table :test #'eql)))
  (declare (type (hash-table-of (integer 1 *) character) decoding-table))
  (setf (gethash 1 decoding-table) #\a)
  (setf (gethash 2 decoding-table) #\b)
  (setf (gethash 3 decoding-table) #\e)
  (setf (gethash 4 decoding-table) #\l)
  (setf (gethash 5 decoding-table) #\s)
  (setf (gethash 6 decoding-table) #\t)
  (setf (gethash 7 decoding-table) #\u)
  
  (let ((goedel-number 41160000))
    (declare (type (integer 1 *) goedel-number))
    
    (let ((encoded-sequence
            (extract-symbol-codes goedel-number))
          (plaintext-sequence
            (goedel-decode goedel-number decoding-table)))
      (declare (type (list-of (integer 1 *)) encoded-sequence))
      (declare (type (list-of character)     plaintext-sequence))
      
      (format T "~&G = ~s" goedel-number)
      (format T "~&T = ~s" encoded-sequence)
      (format T "~&S = ~s" plaintext-sequence))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; -- Example 03: Encoding.                                        -- ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Goedel-encoding of the example from the source [meyer2021goedel3].
;; 
(let ((encoding-table (make-hash-table :test #'eql)))
  (declare (type (hash-table-of character (integer 1 *)) encoding-table))
  (setf (gethash #\{ encoding-table)  4)
  (setf (gethash #\x encoding-table)  6)
  (setf (gethash #\+ encoding-table)  7)
  (setf (gethash #\y encoding-table)  8)
  (setf (gethash #\} encoding-table) 12)
  
  (let ((plaintext-sequence "{x+y}"))
    (declare (type string plaintext-sequence))
    
    (let ((encoded-sequence
            (compute-symbol-codes plaintext-sequence encoding-table))
          (goedel-number
            (goedel-encode plaintext-sequence encoding-table)))
      (declare (type (list-of (integer 1 *)) encoded-sequence))
      (declare (type (integer 0 *)           goedel-number))
      
      (format T "~&S = ~s" plaintext-sequence)
      (format T "~&T = ~s" encoded-sequence)
      (format T "~&G = ~s" goedel-number))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; -- Example 04: Decoding.                                        -- ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Goedel-decoding of the example from the source [meyer2021goedel3].
;; 
(let ((decoding-table (make-hash-table :test #'eql)))
  (declare (type (hash-table-of (integer 1 *) character) decoding-table))
  (setf (gethash  4 decoding-table) #\{)
  (setf (gethash  6 decoding-table) #\x)
  (setf (gethash  7 decoding-table) #\+)
  (setf (gethash  8 decoding-table) #\y)
  (setf (gethash 12 decoding-table) #\})
  
  (let ((goedel-number 16486713209345820741011250000))
    (declare (type (integer 1 *) goedel-number))
    
    (let ((encoded-sequence
            (extract-symbol-codes goedel-number))
          (plaintext-sequence
            (goedel-decode goedel-number decoding-table)))
      (declare (type (list-of (integer 1 *)) encoded-sequence))
      (declare (type (list-of character)     plaintext-sequence))
      
      (format T "~&G = ~s" goedel-number)
      (format T "~&T = ~s" encoded-sequence)
      (format T "~&S = ~s" plaintext-sequence))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; -- Example 05: Goedelang encoding.                              -- ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Encodes the brainfuck "cat program"
;;   ,.[,.]
;; in any of the two version of the esoteric programming language
;; "GÃ¶delang". Yields the resulting Goedel number
;;   59250896327476337572570276385712371250000000000
;; 
;; Please note the following excerpt from GÃ¶delang's instruction set:
;; 
;;   brainfuck command | GÃ¶delang 1/2 value
;;   ------------------+-------------------
;;    .                | 7
;;    ,                | 10
;;    [                | 13
;;    ]                | 14
;; 
(compute-goedel-number '(10 7 13 10 7 14))

;;; -------------------------------------------------------

;; Returns the list
;;   (10 7 13 10 7 14)
;; which represents the "GÃ¶delang" 1 or 2 values associated with the
;; brainfuck command sequence
;;   ,.[,.]
;; implementing an infinitely repeating "cat program".
;; 
(extract-symbol-codes 59250896327476337572570276385712371250000000000)

;;; -------------------------------------------------------

(declaim (type (hash-table-of character (integer 0 *))
               *goedelang-2-encoding-table*))

(defparameter *goedelang-2-encoding-table* (make-hash-table :test #'eql)
  "A Goedel number encoding table which associates with each brainfuck
   command character a numeric value of the Goedelang 2 esoteric
   programming language, representing a symbol code in the form of a
   non-negative integer number.
   ---
   Given a brainfuck instruction sequence to encode, each contained
   command character is translated into its numeric symbol code
   according to this table and, by applying these integers as exponents
   to the first prime numbers, the representative Goedel number will be
   obtained.
   ---
   Note that, for the sake of simplicity, only those mappings have been
   copied from the Goedelang specification whose translation does not
   involve intricacies. This eschews the Goedelang 2 values 9, 11, 15,
   17, and 19.")

(setf (gethash #\Space *goedelang-2-encoding-table*)  0)
(setf (gethash #\>     *goedelang-2-encoding-table*)  1)
(setf (gethash #\<     *goedelang-2-encoding-table*)  2)
(setf (gethash #\+     *goedelang-2-encoding-table*)  3)
(setf (gethash #\-     *goedelang-2-encoding-table*)  5)
(setf (gethash #\.     *goedelang-2-encoding-table*)  7)
(setf (gethash #\,     *goedelang-2-encoding-table*) 10)
(setf (gethash #\[     *goedelang-2-encoding-table*) 13)
(setf (gethash #\]     *goedelang-2-encoding-table*) 14)

(goedel-encode ",.[,.]" *goedelang-2-encoding-table*)



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; -- Example 06: Goedelang decoding.                              -- ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declaim (type (hash-table-of (integer 0 *) character)
               *goedelang-2-decoding-table*))

(defparameter *goedelang-2-decoding-table* (make-hash-table :test #'eql)
  "A Goedel number decoding table which associates with each
   non-negative integer Goedelang 2 value a brainfuck command character.
   ---
   Extracting from a Goedel number, given that it encodes a Goedelang 2
   instruction sequence, the numeric symbol codes, these integers are
   then translated into the associated brainfuck command characters and
   returned in a list.
   ---
   Note that, for the sake of simplicity, only those mappings have been
   copied from the Goedelang specification whose translation does not
   involve intricacies. This eschews the Goedelang 2 values 9, 11, 15,
   17, and 19.")

(setf (gethash  0 *goedelang-2-decoding-table*) #\Space)
(setf (gethash  1 *goedelang-2-decoding-table*) #\>)
(setf (gethash  2 *goedelang-2-decoding-table*) #\<)
(setf (gethash  3 *goedelang-2-decoding-table*) #\+)
(setf (gethash  5 *goedelang-2-decoding-table*) #\-)
(setf (gethash  7 *goedelang-2-decoding-table*) #\.)
(setf (gethash 10 *goedelang-2-decoding-table*) #\,)
(setf (gethash 13 *goedelang-2-decoding-table*) #\[)
(setf (gethash 14 *goedelang-2-decoding-table*) #\])

(coerce
  (goedel-decode 59250896327476337572570276385712371250000000000
                 *goedelang-2-decoding-table*)
  'simple-string)
