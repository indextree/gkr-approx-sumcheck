"""
Standalone finite field implementation for GKR proofs.
Compatible with BN254 scalar field used by ethsnarks.

This provides the FQ class for field arithmetic.
"""

# BN254 scalar field prime (same as used in ethsnarks and circom)
FIELD_MODULUS = 21888242871839275222246405745257275088548364400416034343698204186575808495617


class FQ:
    """
    Finite field element in F_p where p = FIELD_MODULUS (BN254 scalar field)
    """
    
    _field_modulus = FIELD_MODULUS
    
    def __init__(self, val: int):
        if isinstance(val, FQ):
            self.n = val.n
        else:
            self.n = int(val) % self._field_modulus
    
    @classmethod
    def zero(cls) -> 'FQ':
        return cls(0)
    
    @classmethod
    def one(cls) -> 'FQ':
        return cls(1)
    
    @classmethod
    def random(cls) -> 'FQ':
        import secrets
        return cls(secrets.randbelow(cls._field_modulus))
    
    def __repr__(self) -> str:
        return f"FQ({self.n})"
    
    def __str__(self) -> str:
        return str(self.n)
    
    def __int__(self) -> int:
        return self.n
    
    def __hash__(self) -> int:
        return hash(self.n)
    
    def __eq__(self, other) -> bool:
        if isinstance(other, FQ):
            return self.n == other.n
        return self.n == (int(other) % self._field_modulus)
    
    def __ne__(self, other) -> bool:
        return not self.__eq__(other)
    
    def __add__(self, other) -> 'FQ':
        if isinstance(other, FQ):
            return FQ((self.n + other.n) % self._field_modulus)
        return FQ((self.n + int(other)) % self._field_modulus)
    
    def __radd__(self, other) -> 'FQ':
        return self.__add__(other)
    
    def __sub__(self, other) -> 'FQ':
        if isinstance(other, FQ):
            return FQ((self.n - other.n) % self._field_modulus)
        return FQ((self.n - int(other)) % self._field_modulus)
    
    def __rsub__(self, other) -> 'FQ':
        if isinstance(other, FQ):
            return FQ((other.n - self.n) % self._field_modulus)
        return FQ((int(other) - self.n) % self._field_modulus)
    
    def __mul__(self, other) -> 'FQ':
        if isinstance(other, FQ):
            return FQ((self.n * other.n) % self._field_modulus)
        return FQ((self.n * int(other)) % self._field_modulus)
    
    def __rmul__(self, other) -> 'FQ':
        return self.__mul__(other)
    
    def __neg__(self) -> 'FQ':
        return FQ((-self.n) % self._field_modulus)
    
    def __pow__(self, exp) -> 'FQ':
        # Handle FQ exponents by extracting the integer value
        if isinstance(exp, FQ):
            exp = exp.n
        exp = int(exp)
        if exp < 0:
            return self.inv().__pow__(-exp)
        return FQ(pow(self.n, exp, self._field_modulus))
    
    def __rpow__(self, base) -> 'FQ':
        # Handle base ** FQ (where self is the exponent)
        return FQ(pow(int(base), self.n, self._field_modulus))
    
    def __truediv__(self, other) -> 'FQ':
        if isinstance(other, FQ):
            return self * other.inv()
        return self * FQ(other).inv()
    
    def __rtruediv__(self, other) -> 'FQ':
        return FQ(other) * self.inv()
    
    def __floordiv__(self, other) -> 'FQ':
        return self.__truediv__(other)
    
    def __mod__(self, other) -> 'FQ':
        raise TypeError("Modulo not supported for field elements")
    
    def __lt__(self, other) -> bool:
        if isinstance(other, FQ):
            return self.n < other.n
        return self.n < int(other)
    
    def __le__(self, other) -> bool:
        if isinstance(other, FQ):
            return self.n <= other.n
        return self.n <= int(other)
    
    def __gt__(self, other) -> bool:
        if isinstance(other, FQ):
            return self.n > other.n
        return self.n > int(other)
    
    def __ge__(self, other) -> bool:
        if isinstance(other, FQ):
            return self.n >= other.n
        return self.n >= int(other)
    
    def inv(self) -> 'FQ':
        """Modular multiplicative inverse using extended Euclidean algorithm"""
        if self.n == 0:
            raise ZeroDivisionError("Cannot invert zero")
        return FQ(pow(self.n, -1, self._field_modulus))
    
    def is_zero(self) -> bool:
        return self.n == 0
    
    @classmethod
    def from_int(cls, val: int) -> 'FQ':
        return cls(val)
    
    def to_int(self) -> int:
        return self.n
    
    @property
    def val(self) -> int:
        """Alias for n for compatibility"""
        return self.n


# Provide a module-level interface similar to ethsnarks.field
SNARK_SCALAR_FIELD = FIELD_MODULUS
