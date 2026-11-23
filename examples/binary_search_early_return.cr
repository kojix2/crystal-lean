# Binary search with an early return. For sorted xs, returns an index holding
# key or -1 when absent. The generic translator does not recognize its name.
def locate_early(xs : Array(Int32), key : Int32) : Int32
  lo = 0
  hi = xs.size
  while lo < hi
    mid = lo + (hi - lo) // 2
    value = xs[mid]
    if value < key
      lo = mid + 1
    elsif value > key
      hi = mid
    else
      return mid
    end
  end
  -1
end
