# A different binary search: first compute the lower bound, then test it.
# For sorted xs, returns the first matching index or -1 when absent.
def find_first(xs : Array(Int32), target : Int32) : Int32
  left = 0
  right = xs.size
  while left < right
    middle = left + (right - left) // 2
    value = xs[middle]
    if value < target
      left = middle + 1
    else
      right = middle
    end
  end
  if left < xs.size
    if xs[left] == target
      left
    else
      -1
    end
  else
    -1
  end
end
