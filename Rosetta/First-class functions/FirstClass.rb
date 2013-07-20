def f
    a = 1
    b = 3
    [ proc {|xs| xs.map {|x| a * x + b}} \
    , proc {|xs| xs.map {|x| b * x + a}} ]
end

puts f.map {|g| g.call [1, 2, 3, 4, 5]}

