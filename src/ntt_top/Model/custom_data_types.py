import random

class CustomUnsignedInteger:
    def __init__(self, value, min_value=0, max_value=255):
        if not isinstance(value, int):
            raise TypeError("Value must be an integer.")
        if not (min_value <= value <= max_value):
            raise ValueError(f"Value must be within the range {min_value}-{max_value}.")
        self.value = value
        self.min_value = min_value
        self.max_value = max_value

    def __str__(self):
        return str(self.value)

    def __repr__(self):
        return f"CustomUnsignedInteger({self.value}, {self.min_value}, {self.max_value})"

    def __add__(self, other):
        if isinstance(other, CustomUnsignedInteger):
            result = self.value + other.value
            return CustomUnsignedInteger(result % (self.max_value + 1), self.min_value, self.max_value)
        elif isinstance(other, int):
            result = self.value + other
            return CustomUnsignedInteger(result % (self.max_value + 1), self.min_value, self.max_value)
        else:
            raise TypeError("Unsupported operand type for +.")

    def __sub__(self, other):
        if isinstance(other, CustomUnsignedInteger):
            result = self.value - other.value
            return CustomUnsignedInteger((result + (self.max_value + 1)) % (self.max_value + 1), self.min_value, self.max_value)
        elif isinstance(other, int):
            result = self.value - other
            return CustomUnsignedInteger((result + (self.max_value + 1)) % (self.max_value + 1), self.min_value, self.max_value)
        else:
            raise TypeError("Unsupported operand type for -.")

    def __mul__(self, other):
        if isinstance(other, CustomUnsignedInteger):
            result = self.value * other.value
            return CustomUnsignedInteger(result % (self.max_value + 1), self.min_value, self.max_value)
        elif isinstance(other, int):
            result = self.value * other
            return CustomUnsignedInteger(result % (self.max_value + 1), self.min_value, self.max_value)
        else:
            raise TypeError("Unsupported operand type for *.")

    def generate_random(self):
        self.value = random.randint(self.min_value, self.max_value)

    def __int__(self):
        if self.value is not None:
            return self.value
        else:
            raise TypeError("CustomUnsignedInteger value is None.")
        

import numpy as np

class BitSplitter:
    def __init__(self, number, num_bits):
        """
        Initialize the BitSplitter with an integer and the number of bits.
        
        :param number: The integer number to split into bits.
        :param num_bits: The number of bits to consider for the binary representation.
        """
        self.number = number
        self.num_bits = num_bits
        self.bits = self.split_to_bits()
        self.Y = self.reverse_bits()

    def split_to_bits(self):
        """
        Split the integer into a numpy array of bits according to num_bits.
        
        :return: A numpy array of bits (0 or 1) from the most significant to the least significant.
        """
        bits = [(self.number >> i) & 1 for i in range(self.num_bits-1, -1, -1)]
        return np.array(bits, dtype=np.uint8)
    
    def reverse_bits(self):
        """
        Reverse the entire bit array to represent bits from LSB to MSB.
        
        :return: Reversed numpy array of bits.
        """
        return self.bits[::-1]
    
    def get_slice(self, high, low):
        """
        Get a slice of the reversed bit array, from high to low (inclusive).
        
        :param high: High index of the slice (inclusive).
        :param low: Low index of the slice (inclusive).
        :return: A numpy array representing the slice from high to low bits of the reversed array Y.
        """
        # Check for index bounds and logic
        if high < low or high >= self.num_bits or low < 0:
            raise ValueError("Invalid high or low indices for bit slice.")
        # Fetch directly from Y
        return self.Y[low:high + 1][::-1]


    @staticmethod
    def bits_to_int(bits_array):
        """
        Convert a numpy array of bits back into an integer, independently of the array's length.
        
        :param bits_array: A numpy array of bits to be converted.
        :return: Integer value of the binary number represented by the bits array.
        """
        return int(''.join(bits_array.astype(str)), 2)
    

    @staticmethod
    def leftpadding(bits_array, numOfZeros):
        padded_array = np.pad(bits_array, (numOfZeros, 0), 'constant', constant_values=(0, 0))
        return padded_array
    
    @staticmethod
    def rightpadding(bits_array, numOfZeros):
        padded_array = np.pad(bits_array, (0, numOfZeros), 'constant', constant_values=(0, 0))
        return padded_array



    def __repr__(self):
        return f"Number: {self.number} (Binary: {''.join(map(str, self.bits))})"



def get_slice(bits_array, high, low):
    Y = bits_array[::-1]
    shape = Y.shape
    size = shape[0]
    # Check for index bounds and logic
    if high < low or high >= size or low < 0:
        raise ValueError("Invalid high or low indices for bit slice.")
    # Fetch directly from Y
    return Y[low:high + 1][::-1]




