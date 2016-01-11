# raise

#raise "This is a message"

#raise ArgumentError, "illegal arguments!"

#raise ArgumentError.new("Illegal arguments!")

class ParseError < Exception
  def initialize input, line, pos
    super "Could not parse '#{input}' at line #{line}, position #{pos}"
  end
end

#raise ParseError.new("Foo", 3, 9)

begin
  # do something
rescue
  # handle exception
else
  # do this if no exception was raised
ensure
  # do this whether or not exception was raised
end

begin
  # do something
rescue Exception
  # exception handling code here
  # don't write only 'rescue'; that only catches StandardError, a subclass of Exception
end

begin

rescue RuntimeError

end

begin 

rescue RuntimeError => e

end

begin

rescue RuntimeError, Timeout::Error => e

end








