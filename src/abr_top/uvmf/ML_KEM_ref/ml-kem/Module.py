class Module:
    def __init__(self, ring):
        """
        Initialise a module over the ring ``ring``.
        """
        self.ring = ring
        self.matrix = Matrix

    def random_element(self, m, n):
        """
        Generate a random element of the module of dimension m x n

        :param int m: the number of rows in the matrix
        :param int m: the number of columns in tge matrix
        :return: an element of the module with dimension `m times n`
        """
        elements = [
            [self.ring.random_element() for _ in range(n)] for _ in range(m)
        ]
        return self(elements)

    def __repr__(self):
        return f"Module over the commutative ring: {self.ring}"

    def __str__(self):
        return f"Module over the commutative ring: {self.ring}"

    def __call__(self, matrix_elements, transpose=False):
        if not isinstance(matrix_elements, list):
            raise TypeError(
                "elements of a module are matrices, built from elements of the base ring"
            )

        if isinstance(matrix_elements[0], list):
            for element_list in matrix_elements:
                if not all(
                    isinstance(aij, self.ring.element) for aij in element_list
                ):
                    raise TypeError(
                        f"All elements of the matrix must be elements of the ring: {self.ring}"
                    )
            return self.matrix(self, matrix_elements, transpose=transpose)

        elif isinstance(matrix_elements[0], self.ring.element):
            if not all(
                isinstance(aij, self.ring.element) for aij in matrix_elements
            ):
                raise TypeError(
                    f"All elements of the matrix must be elements of the ring: {self.ring}"
                )
            return self.matrix(self, [matrix_elements], transpose=transpose)

        else:
            raise TypeError(
                "elements of a module are matrices, built from elements of the base ring"
            )

    def vector(self, elements):
        """
        Construct a vector given a list of elements of the module's ring

        :param list: a list of elements of the ring
        :return: a vector of the module
        """
        return self.matrix(self, [elements], transpose=True)


class Matrix:
    def __init__(self, parent, matrix_data, transpose=False):
        self.parent = parent
        self._data = matrix_data
        self._transpose = transpose
        if not self._check_dimensions():
            raise ValueError("Inconsistent row lengths in matrix")

    def dim(self):
        """
        Return the dimensions of the matrix with m rows
        and n columns

        :return: the dimension of the matrix ``(m, n)``
        :rtype: tuple(int, int)
        """
        if not self._transpose:
            return len(self._data), len(self._data[0])
        else:
            return len(self._data[0]), len(self._data)

    def _check_dimensions(self):
        """
        Ensure that the matrix is rectangular
        """
        return len(set(map(len, self._data))) == 1

    def transpose(self):
        """
        Return a matrix with the rows and columns of swapped
        """
        return self.parent(self._data, not self._transpose)

    def transpose_self(self):
        """
        Swap the rows and columns of the matrix in place
        """
        self._transpose = not self._transpose
        return

    T = property(transpose)

    def reduce_coefficients(self):
        """
        Reduce every element in the polynomial
        using the modulus of the PolynomialRing
        """
        for row in self._data:
            for ele in row:
                ele.reduce_coefficients()
        return self

    def __getitem__(self, idx):
        """
        matrix[i, j] returns the element on row i, column j
        """
        assert (
            isinstance(idx, tuple) and len(idx) == 2
        ), "Can't access individual rows"
        if not self._transpose:
            return self._data[idx[0]][idx[1]]
        else:
            return self._data[idx[1]][idx[0]]

    def __eq__(self, other):
        if self.dim() != other.dim():
            return False
        m, n = self.dim()
        return all(
            [self[i, j] == other[i, j] for i in range(m) for j in range(n)]
        )

    def __neg__(self):
        """
        Returns -self, by negating all elements
        """
        m, n = self.dim()
        return self.parent(
            [[-self[i, j] for j in range(n)] for i in range(m)],
            self._transpose,
        )

    def __add__(self, other):
        if not isinstance(other, type(self)):
            raise TypeError("Can only add matrices to other matrices")
        if self.parent != other.parent:
            raise TypeError("Matrices must have the same base ring")
        if self.dim() != other.dim():
            raise ValueError("Matrices are not of the same dimensions")

        m, n = self.dim()
        return self.parent(
            [[self[i, j] + other[i, j] for j in range(n)] for i in range(m)],
            False,
        )

    def __iadd__(self, other):
        self = self + other
        return self

    def __sub__(self, other):
        if not isinstance(other, type(self)):
            raise TypeError("Can only add matrices to other matrices")
        if self.parent != other.parent:
            raise TypeError("Matrices must have the same base ring")
        if self.dim() != other.dim():
            raise ValueError("Matrices are not of the same dimensions")

        m, n = self.dim()
        return self.parent(
            [[self[i, j] - other[i, j] for j in range(n)] for i in range(m)],
            False,
        )

    def __isub__(self, other):
        self = self - other
        return self

    def __matmul__(self, other):
        """
        Denoted A @ B
        """
        if not isinstance(other, type(self)):
            raise TypeError("Can only multiply matrcies with other matrices")
        if self.parent != other.parent:
            raise TypeError("Matrices must have the same base ring")

        m, n = self.dim()
        n_, l = other.dim()
        if not n == n_:
            raise ValueError("Matrices are of incompatible dimensions")

        return self.parent(
            [
                [
                    sum(self[i, k] * other[k, j] for k in range(n))
                    for j in range(l)
                ]
                for i in range(m)
            ]
        )

    def dot(self, other):
        """
        Compute the inner product of two vectors
        """
        if not isinstance(other, type(self)):
            raise TypeError("Can only perform dot product with other matrices")
        res = self.T @ other
        assert res.dim() == (1, 1)
        return res[0, 0]

    def __repr__(self):
        m, n = self.dim()

        if m == 1:
            return str(self._data[0])

        max_col_width = [
            max(len(str(self[i, j])) for i in range(m)) for j in range(n)
        ]
        info = "]\n[".join(
            [
                ", ".join(
                    [
                        f"{str(self[i, j]):>{max_col_width[j]}}"
                        for j in range(n)
                    ]
                )
                for i in range(m)
            ]
        )
        return f"[{info}]"
    


import random


class PolynomialRing:
    """
    Initialise the polynomial ring:

        R = GF(q) / (X^n + 1)
    """

    def __init__(self, q, n):
        self.q = q
        self.n = n
        self.element = Polynomial

    def gen(self):
        """
        Return the generator `x` of the polynomial ring
        """
        return self([0, 1])

    def random_element(self):
        """
        Compute a random element of the polynomial ring with coefficients in the
        canonical range: ``[0, q-1]``
        """
        coefficients = [random.randint(0, self.q - 1) for _ in range(self.n)]
        return self(coefficients)

    def __call__(self, coefficients):
        if isinstance(coefficients, int):
            return self.element(self, [coefficients])
        if not isinstance(coefficients, list):
            raise TypeError(
                f"Polynomials should be constructed from a list of integers, of length at most d = {self.n}"
            )
        return self.element(self, coefficients)

    def __repr__(self):
        return f"Univariate Polynomial Ring in x over Finite Field of size {self.q} with modulus x^{self.n} + 1"


class Polynomial:
    def __init__(self, parent, coefficients):
        self.parent = parent
        self.coeffs = self._parse_coefficients(coefficients)

    def is_zero(self):
        """
        Return if polynomial is zero: f = 0
        """
        return all(c == 0 for c in self.coeffs)

    def is_constant(self):
        """
        Return if polynomial is constant: f = c
        """
        return all(c == 0 for c in self.coeffs[1:])

    def _parse_coefficients(self, coefficients):
        """
        Helper function which right pads with zeros
        to allow polynomial construction as
        f = R([1,1,1])
        """
        l = len(coefficients)
        if l > self.parent.n:
            raise ValueError(
                f"Coefficients describe polynomial of degree greater than maximum degree {self.parent.n}"
            )
        elif l < self.parent.n:
            coefficients = coefficients + [0 for _ in range(self.parent.n - l)]
        return coefficients

    def reduce_coefficients(self):
        """
        Reduce all coefficients modulo q
        """
        self.coeffs = [c % self.parent.q for c in self.coeffs]
        return self

    def _add_mod_q(self, x, y):
        """
        add two coefficients modulo q
        """
        return (x + y) % self.parent.q

    def _sub_mod_q(self, x, y):
        """
        sub two coefficients modulo q
        """
        return (x - y) % self.parent.q

    def _schoolbook_multiplication(self, other):
        """
        Naive implementation of polynomial multiplication
        suitible for all R_q = F_1[X]/(X^n + 1)
        """
        n = self.parent.n
        a = self.coeffs
        b = other.coeffs
        new_coeffs = [0 for _ in range(n)]
        for i in range(n):
            for j in range(0, n - i):
                new_coeffs[i + j] += a[i] * b[j]
        for j in range(1, n):
            for i in range(n - j, n):
                new_coeffs[i + j - n] -= a[i] * b[j]
        return [c % self.parent.q for c in new_coeffs]

    def __neg__(self):
        """
        Returns -f, by negating all coefficients
        """
        neg_coeffs = [(-x % self.parent.q) for x in self.coeffs]
        return self.parent(neg_coeffs)

    def _add_(self, other):
        if isinstance(other, type(self)):
            new_coeffs = [
                self._add_mod_q(x, y)
                for x, y in zip(self.coeffs, other.coeffs)
            ]
        elif isinstance(other, int):
            new_coeffs = self.coeffs.copy()
            new_coeffs[0] = self._add_mod_q(new_coeffs[0], other)
        else:
            raise NotImplementedError(
                "Polynomials can only be added to each other"
            )
        return new_coeffs

    def __add__(self, other):
        new_coeffs = self._add_(other)
        return self.parent(new_coeffs)

    def __radd__(self, other):
        return self.__add__(other)

    def __iadd__(self, other):
        self = self + other
        return self

    def _sub_(self, other):
        if isinstance(other, type(self)):
            new_coeffs = [
                self._sub_mod_q(x, y)
                for x, y in zip(self.coeffs, other.coeffs)
            ]
        elif isinstance(other, int):
            new_coeffs = self.coeffs.copy()
            new_coeffs[0] = self._sub_mod_q(new_coeffs[0], other)
        else:
            raise NotImplementedError(
                "Polynomials can only be subtracted from each other"
            )
        return new_coeffs

    def __sub__(self, other):
        new_coeffs = self._sub_(other)
        return self.parent(new_coeffs)

    def __rsub__(self, other):
        return -self.__sub__(other)

    def __isub__(self, other):
        self = self - other
        return self

    def __mul__(self, other):
        if isinstance(other, type(self)):
            new_coeffs = self._schoolbook_multiplication(other)
        elif isinstance(other, int):
            new_coeffs = [(c * other) % self.parent.q for c in self.coeffs]
        else:
            raise NotImplementedError(
                "Polynomials can only be multiplied by each other, or scaled by integers"
            )
        return self.parent(new_coeffs)

    def __rmul__(self, other):
        return self.__mul__(other)

    def __imul__(self, other):
        self = self * other
        return self

    def __pow__(self, n):
        if not isinstance(n, int):
            raise TypeError(
                "Exponentiation of a polynomial must be done using an integer."
            )

        # Deal with negative scalar multiplication
        if n < 0:
            raise ValueError(
                "Negative powers are not supported for elements of a Polynomial Ring"
            )
        f = self
        g = self.parent(1)
        while n > 0:
            if n % 2 == 1:
                g = g * f
            f = f * f
            n = n // 2
        return g

    def __eq__(self, other):
        if isinstance(other, type(self)):
            return self.coeffs == other.coeffs
        elif isinstance(other, int):
            if (
                self.is_constant()
                and (other % self.parent.q) == self.coeffs[0]
            ):
                return True
        return False

    def __getitem__(self, idx):
        return self.coeffs[idx]

    def __repr__(self):
        if self.is_zero():
            return "0"

        info = []
        for i, c in enumerate(self.coeffs):
            if c != 0:
                if i == 0:
                    info.append(f"{c}")
                elif i == 1:
                    if c == 1:
                        info.append("x")
                    else:
                        info.append(f"{c}*x")
                else:
                    if c == 1:
                        info.append(f"x^{i}")
                    else:
                        info.append(f"{c}*x^{i}")
        return " + ".join(info)

    def __str__(self):
        return self.__repr__()
    

from utils import bit_count


class PolynomialRingKyber(PolynomialRing):
    """
    Initialise the polynomial ring:

        R = GF(3329) / (X^256 + 1)
    """

    def __init__(self):
        self.q = 3329
        self.n = 256
        self.element = PolynomialKyber
        self.element_ntt = PolynomialKyberNTT

        root_of_unity = 17
        self.ntt_zetas = [
            pow(root_of_unity, self._br(i, 7), 3329) for i in range(128)
        ]
        self.ntt_f = pow(128, -1, 3329)

    @staticmethod
    def _br(i, k):
        """
        bit reversal of an unsigned k-bit integer
        """
        bin_i = bin(i & (2**k - 1))[2:].zfill(k)
        return int(bin_i[::-1], 2)

    def ntt_sample(self, input_bytes):
        """
        Algorithm 1 (Parse)
        https://pq-crystals.org/kyber/data/kyber-specification-round3-20210804.pdf

        Algorithm 6 (Sample NTT)

        Parse: B^* -> R
        """
        i, j = 0, 0
        coefficients = [0 for _ in range(self.n)]
        while j < self.n:
            d1 = input_bytes[i] + 256 * (input_bytes[i + 1] % 16)
            d2 = (input_bytes[i + 1] // 16) + 16 * input_bytes[i + 2]

            if d1 < 3329:
                coefficients[j] = d1
                j = j + 1

            if d2 < 3329 and j < self.n:
                coefficients[j] = d2
                j = j + 1

            i = i + 3
        return self(coefficients, is_ntt=True)

    def cbd(self, input_bytes, eta, is_ntt=False):
        """
        Algorithm 2 (Centered Binomial Distribution)
        https://pq-crystals.org/kyber/data/kyber-specification-round3-20210804.pdf

        Algorithm 6 (Sample Poly CBD)

        Expects a byte array of length (eta * deg / 4)
        For Kyber, this is 64 eta.
        """
        assert 64 * eta == len(input_bytes)
        coefficients = [0 for _ in range(256)]
        b_int = int.from_bytes(input_bytes, "little")
        mask = (1 << eta) - 1
        mask2 = (1 << 2 * eta) - 1
        for i in range(256):
            x = b_int & mask2
            a = bit_count(x & mask)
            b = bit_count((x >> eta) & mask)
            b_int >>= 2 * eta
            coefficients[i] = (a - b) % 3329
        return self(coefficients, is_ntt=is_ntt)

    def decode(self, input_bytes, d, is_ntt=False):
        """
        Decode (Algorithm 3)

        decode: B^32l -> R_q
        """
        # Ensure the value d is set correctly
        if 256 * d != len(input_bytes) * 8:
            raise ValueError(
                f"input bytes must be a multiple of (polynomial degree) / 8, {256*d = }, {len(input_bytes)*8 = }"
            )

        # Set the modulus
        if d == 12:
            m = 3329
        else:
            m = 1 << d

        coeffs = [0 for _ in range(256)]
        b_int = int.from_bytes(input_bytes, "little")
        mask = (1 << d) - 1
        for i in range(256):
            coeffs[i] = (b_int & mask) % m
            b_int >>= d

        return self(coeffs, is_ntt=is_ntt)

    def __call__(self, coefficients, is_ntt=False):
        if not is_ntt:
            element = self.element
        else:
            element = self.element_ntt

        if isinstance(coefficients, int):
            return element(self, [coefficients])
        if not isinstance(coefficients, list):
            raise TypeError(
                f"Polynomials should be constructed from a list of integers, of length at most n = {256}"
            )
        return element(self, coefficients)


class PolynomialKyber(Polynomial):
    def __init__(self, parent, coefficients):
        self.parent = parent
        self.coeffs = self._parse_coefficients(coefficients)

    def encode(self, d):
        """
        Encode (Inverse of Algorithm 3)
        """
        t = 0
        for i in range(255):
            t |= self.coeffs[256 - i - 1]
            t <<= d
        t |= self.coeffs[0]
        return t.to_bytes(32 * d, "little")

    def _compress_ele(self, x, d):
        """
        Compute round((2^d / q) * x) % 2^d
        """
        t = 1 << d
        y = (t * x + 1664) // 3329  # 1664 = 3329 // 2
        return y % t

    def _decompress_ele(self, x, d):
        """
        Compute round((q / 2^d) * x)
        """
        t = 1 << (d - 1)
        y = (3329 * x + t) >> d
        return y

    def compress(self, d):
        """
        Compress the polynomial by compressing each coefficient

        NOTE: This is lossy compression
        """
        self.coeffs = [self._compress_ele(c, d) for c in self.coeffs]
        return self

    def decompress(self, d):
        """
        Decompress the polynomial by decompressing each coefficient

        NOTE: This as compression is lossy, we have
        x' = decompress(compress(x)), which x' != x, but is
        close in magnitude.
        """
        self.coeffs = [self._decompress_ele(c, d) for c in self.coeffs]
        return self

    def to_ntt(self):
        """
        Convert a polynomial to number-theoretic transform (NTT) form.
        The input is in standard order, the output is in bit-reversed order.
        """
        k, l = 1, 128
        coeffs = self.coeffs
        zetas = self.parent.ntt_zetas
        while l >= 2:
            start = 0
            while start < 256:
                zeta = zetas[k]
                k = k + 1
                for j in range(start, start + l):
                    t = zeta * coeffs[j + l]
                    coeffs[j + l] = coeffs[j] - t
                    coeffs[j] = coeffs[j] + t
                start = l + (j + 1)
            l = l >> 1

        for j in range(256):
            coeffs[j] = coeffs[j] % 3329

        return self.parent(coeffs, is_ntt=True)

    def from_ntt(self):
        """
        Not supported, raises a ``TypeError``
        """
        raise TypeError(f"Polynomial not in the NTT domain: {type(self) = }")


class PolynomialKyberNTT(PolynomialKyber):
    def __init__(self, parent, coefficients):
        self.parent = parent
        self.coeffs = self._parse_coefficients(coefficients)

    def to_ntt(self):
        """
        Not supported, raises a ``TypeError``
        """
        raise TypeError(
            f"Polynomial is already in the NTT domain: {type(self) = }"
        )

    def from_ntt(self):
        """
        Convert a polynomial from number-theoretic transform (NTT) form in place
        The input is in bit-reversed order, the output is in standard order.
        """
        l, l_upper = 2, 128
        k = l_upper - 1
        coeffs = self.coeffs
        zetas = self.parent.ntt_zetas
        while l <= 128:
            start = 0
            while start < 256:
                zeta = zetas[k]
                k = k - 1
                for j in range(start, start + l):
                    t = coeffs[j]
                    coeffs[j] = t + coeffs[j + l]
                    coeffs[j + l] = coeffs[j + l] - t
                    coeffs[j + l] = zeta * coeffs[j + l]
                start = j + l + 1
            l = l << 1

        f = self.parent.ntt_f
        for j in range(256):
            coeffs[j] = (coeffs[j] * f) % 3329

        return self.parent(coeffs, is_ntt=False)

    @staticmethod
    def _ntt_base_multiplication(a0, a1, b0, b1, zeta):
        """
        Base case for ntt multiplication
        """
        r0 = (a0 * b0 + zeta * a1 * b1) % 3329
        r1 = (a1 * b0 + a0 * b1) % 3329
        return r0, r1

    def _ntt_coefficient_multiplication(self, f_coeffs, g_coeffs):
        """
        Given the coefficients of two polynomials compute the coefficients of
        their product
        """
        new_coeffs = []
        zetas = self.parent.ntt_zetas
        for i in range(64):
            r0, r1 = self._ntt_base_multiplication(
                f_coeffs[4 * i + 0],
                f_coeffs[4 * i + 1],
                g_coeffs[4 * i + 0],
                g_coeffs[4 * i + 1],
                zetas[64 + i],
            )
            r2, r3 = self._ntt_base_multiplication(
                f_coeffs[4 * i + 2],
                f_coeffs[4 * i + 3],
                g_coeffs[4 * i + 2],
                g_coeffs[4 * i + 3],
                -zetas[64 + i],
            )
            new_coeffs += [r0, r1, r2, r3]
        return new_coeffs

    def _ntt_multiplication(self, other):
        """
        Number Theoretic Transform multiplication.
        """
        new_coeffs = self._ntt_coefficient_multiplication(
            self.coeffs, other.coeffs
        )
        return new_coeffs

    def __add__(self, other):
        new_coeffs = self._add_(other)
        return self.parent(new_coeffs, is_ntt=True)

    def __sub__(self, other):
        new_coeffs = self._sub_(other)
        return self.parent(new_coeffs, is_ntt=True)

    def __mul__(self, other):
        if isinstance(other, type(self)):
            new_coeffs = self._ntt_multiplication(other)
        elif isinstance(other, int):
            new_coeffs = [(c * other) % 3329 for c in self.coeffs]
        else:
            raise NotImplementedError(
                f"Polynomials can only be multiplied by each other, or scaled by integers, {type(other) = }, {type(self) = }"
            )
        return self.parent(new_coeffs, is_ntt=True)
    

class ModuleKyber(Module):
    def __init__(self):
        self.ring = PolynomialRingKyber()
        self.matrix = MatrixKyber

    def decode_vector(self, input_bytes, k, d, is_ntt=False):
        """
        Decode bytes into a a vector of polynomial elements.

        Each element is assumed to be encoded as a polynomial with ``d``-bit
        coefficients (hence a polynomial is encoded into ``256 * d`` bits).

        A vector of length ``k`` then has ``256 * d * k`` bits.
        """
        # Ensure the input bytes are the correct length to create k elements with
        # d bits used for each coefficient
        if self.ring.n * d * k != len(input_bytes) * 8:
            raise ValueError(
                "Byte length is the wrong length for given k, d values"
            )

        # Bytes needed to decode a polynomial
        n = 32 * d

        # Encode each chunk of bytes as a polynomial and create the vector
        elements = [
            self.ring.decode(input_bytes[i : i + n], d, is_ntt=is_ntt)
            for i in range(0, len(input_bytes), n)
        ]

        return self.vector(elements)


class MatrixKyber(Matrix):
    def __init__(self, parent, matrix_data, transpose=False):
        super().__init__(parent, matrix_data, transpose=transpose)

    def encode(self, d):
        """
        Encode every element of a matrix into bytes and concatenate
        """
        output = b""
        for row in self._data:
            for ele in row:
                output += ele.encode(d)
        return output

    def compress(self, d):
        """
        Compress every element of the matrix to have at most ``d`` bits
        """
        for row in self._data:
            for ele in row:
                ele.compress(d)
        return self

    def decompress(self, d):
        """
        Perform (lossy) decompression of the polynomial assuming it has been
        compressed to have at most ``d`` bits.
        """
        for row in self._data:
            for ele in row:
                ele.decompress(d)
        return self

    def to_ntt(self):
        """
        Convert every element of the matrix into NTT form
        """
        data = [[x.to_ntt() for x in row] for row in self._data]
        return self.parent(data, transpose=self._transpose)

    def from_ntt(self):
        """
        Convert every element of the matrix from NTT form
        """
        data = [[x.from_ntt() for x in row] for row in self._data]
        return self.parent(data, transpose=self._transpose)