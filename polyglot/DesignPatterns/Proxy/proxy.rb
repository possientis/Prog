# Proxy Design Pattern

# This code exercise is borrowed from Design Patterns in C# - 13 Proxy 
# https://www.youtube.com/watch?v=XvbDqLrnkmA

# A proxy is a class which functions as an interface to something else

# There are three participants to the proxy design pattern:
#
# 1. subject
# 2. real subject
# 3. proxy
#

# The subject is the common interface between the real object and proxy
# the real object is that which the proxy is meant to be substituted for

# This is the subject
class ComponentPrice
  attr_reader :CpuPrice, :RamPrice, :SsdPrice
  def CpuPrice() raise  NotImplementedError.new "" end
  def RamPrice() raise  NotImplementedError.new "" end
  def SsdPrice() raise  NotImplementedError.new "" end
end

# This is the real subject
class StoredComponentPrice < ComponentPrice
  def CpuPrice() return 250.0 end
  def RamPrice() return 32.0  end
  def SsdPrice() return 225.0 end
end

# This is the proxy
class ProxyComponentPrice < ComponentPrice
  def CpuPrice() return requestFromServer("CPU") end
  def RamPrice() return requestFromServer("RAM") end
  def SsdPrice() return requestFromServer("SSD") end
  def requestFromServer(request) 
    return Server.getInstance.sendRequest(request)
  end
end

class Server
  @@instance = nil
  def self.getInstance() return @@instance end
  def self.startServer() @@instance = Server.new end

  def initialize()
    puts "Component price server running, awaiting request"
  end
  def sendRequest(request)
    puts "Server receiving request for #{request} price"
    # In our example, server uses real subject
    component = StoredComponentPrice.new  # real subject
    puts "Server responding to request for #{request} price"  
    case request
    when "CPU"
      return component.CpuPrice
    when "RAM"
      return component.RamPrice
    when "SSD"
      return component.SsdPrice
    else
      raise Exception.new "Server: invalid request"
    end
  end
end

Server.startServer
# we can use proxy as if it was real, making client code a lot simpler
prices = ProxyComponentPrice.new
cpu = prices.CpuPrice
ram = prices.RamPrice
ssd = prices.SsdPrice
puts "The CPU price is #{cpu}"
puts "The RAM price is #{ram}"
puts "The SSD price is #{ssd}"





