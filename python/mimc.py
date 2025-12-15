"""
MiMC hash function implementation (simplified for testing).
Compatible with the ethsnarks.mimc module interface.

MiMC is a ZK-friendly hash function used for Fiat-Shamir transformation.
"""

from field import FQ, FIELD_MODULUS

# MiMC round constants (sample - in production use proper constants)
MIMC_ROUNDS = 91
MIMC_CONSTANTS = []

def _generate_round_constants():
    """Generate MiMC round constants"""
    global MIMC_CONSTANTS
    if not MIMC_CONSTANTS:
        # Simple deterministic generation for testing
        # In production, use secure constants
        import hashlib
        for i in range(MIMC_ROUNDS):
            h = hashlib.sha256(f"mimc_constant_{i}".encode()).digest()
            MIMC_CONSTANTS.append(int.from_bytes(h, 'big') % FIELD_MODULUS)

_generate_round_constants()


def mimc_round(x: int, k: int, c: int) -> int:
    """Single MiMC round: (x + k + c)^7 mod p"""
    return pow((x + k + c) % FIELD_MODULUS, 7, FIELD_MODULUS)


def mimc_hash(inputs, seed: int = 0) -> int:
    """
    MiMC hash function (sponge construction).
    
    Args:
        inputs: List of integers or FQ elements to hash
        seed: Optional seed value
    
    Returns:
        Hash output as integer
    """
    if not inputs:
        return seed
    
    # Convert inputs to integers
    int_inputs = []
    for x in inputs:
        if isinstance(x, FQ):
            int_inputs.append(x.n)
        else:
            int_inputs.append(int(x))
    
    # Initial state
    state = seed
    
    # Process each input
    for inp in int_inputs:
        key = inp
        x = state
        
        # Apply MiMC rounds
        for i in range(MIMC_ROUNDS):
            x = mimc_round(x, key, MIMC_CONSTANTS[i])
        
        # Update state (sponge absorption)
        state = (state + x + key) % FIELD_MODULUS
    
    return state


def mimc_encrypt(x: int, key: int) -> int:
    """
    MiMC encryption.
    
    Args:
        x: Plaintext as integer
        key: Key as integer
    
    Returns:
        Ciphertext as integer
    """
    for i in range(MIMC_ROUNDS):
        x = mimc_round(x, key, MIMC_CONSTANTS[i])
    return (x + key) % FIELD_MODULUS


# Make it compatible with ethsnarks interface
class MiMC:
    """MiMC hasher class"""
    
    def __init__(self, seed: int = 0):
        self.seed = seed
    
    def hash(self, *inputs) -> int:
        return mimc_hash(list(inputs), self.seed)


# Module-level convenience function
def hash(*inputs, seed: int = 0) -> int:
    return mimc_hash(list(inputs), seed)
