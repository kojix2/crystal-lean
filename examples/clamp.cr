# Control flow and returns without array access or a loop.
def clamp_score(value : Int32) : Int32
  if value < 0
    0
  elsif value > 100
    100
  else
    value
  end
end
