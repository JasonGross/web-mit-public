def gcd(a, *nums):
    if len(nums) == 0: return a
    b = nums[0]
    a, b = abs(a), abs(b)
    if a < b: a, b = b, a
    while b > 0:
        a, b = b, a % b
    return gcd(a, *nums[1:])

def product(*nums):
    rtn = 1
    for num in nums:
        rtn *= num
    return rtn

def lcm(a, *nums):
    if len(nums) == 0: return a
    b = nums[0]
    return lcm(a * b // gcd(a, b),
               *nums[1:])
