puts "Hello, world!"
puts -199.abs
puts "ice is nice".length
puts "ruby is cool.".index("y")
#puts "Nice Day Isn't It?".downcase.split("").uniq.sort.join
print "Please type name>"
#name = gets.chomp
#puts "Hello #{name}."
puts "Give me a number"
#number = gets.chomp
#puts number.to_i
#outnum = number.to_i + 1
#puts outnum.to_s + ' is a bigger number'
a = "\nThis is a double-quoted string\n"
b = %Q{\nThis is a double-quoted string\n}
c = %{\nThis is a double-quoted string\n}
d = %/\nThis is a double-quoted string\n/
e = 'This is a single-quoted string'
f = %q{This is a single-quoted string}

var = 3.14159
puts "pi is #{var}"

a = [1, 'hi', 3.14, 1, 2, [4,5]]

puts a[2]
puts a.[](2)
print a
puts ""
print a.reverse
puts ""
print a.flatten.uniq
puts ""

a = Hash.new
b = {}
a = {:water => 'wet', :fire => 'hot'}
puts a[:water]
puts a[:unknown] == nil

a.each_pair do |key,value|
  puts "#{key} is #{value}"
end

puts "-----"
a.each {|key,value| puts "#{key} is #{value}"}

a.delete :water
print a
puts ""

a.delete_if {|key,value| value == 'hot'}
print a

if rand(100) % 2 == 0 
  puts "It's even"
else
  puts "It's odd"
end

File.open('test.dat','w') do |file|
  file.puts "wrote some text"
  file.puts "writing a second line"
  file.puts "and a third"
end

File.readlines('test.dat').each do |line|
  puts line
end

def remember(&a_block)
  @block = a_block
end
remember {|name| puts "Hello, #{name}!"}
@block.call('John')

a = proc {|arg| puts arg}
a.call("oioi")

a = Proc.new{|arg| puts arg}
a.call("this is me again")

a = lambda{|arg| puts arg}
a.call("well, well, well")

a = ->(arg){puts arg}
a.call("Hopefully my last call")

def create_set_and_get(initial_value=0)
  closure_value = initial_value
  [Proc.new{|x| closure_value = x}, Proc.new{closure_value}]
end

setter, getter = create_set_and_get
puts getter.call
setter.call(21)
puts getter.call

# This makes no sense
def use_hello
  yield "hello"
end
use_hello {|string| puts string}
# I did not get this

array = [1,'hi',3.14]
array.each {|item| puts item}

array.each_index {|index| puts "#{index}: #{array[index]}"}
(3..6).each {|num| puts num}
(3...6).each{|num| puts num}  # excludes 6

puts [1,3,5].inject(10) {|sum,element| sum + element} # foldL 10 (+)

print (1..10).collect {|x| x*x} # map (\x -> x*x} [1..10]
puts 
print (1..10).map {|x| x*x}
puts
print (1..5).map {|x| x.to_f}
puts
print ((1..5).map do |x| x.to_f end)
puts
print (1..5).map(&:to_f)


