# In-place bubble sort, using only local Int32 counters and array access.
# The generic compiler models this program; it does not recognize its name.
def bubble_sort(xs : Array(Int32)) : Array(Int32)
  size = xs.size
  pass = 0
  while pass < size
    position = 0
    while position + 1 < size
      if xs[position] > xs[position + 1]
        temporary = xs[position]
        xs[position] = xs[position + 1]
        xs[position + 1] = temporary
      end
      position = position + 1
    end
    pass = pass + 1
  end
  xs
end
