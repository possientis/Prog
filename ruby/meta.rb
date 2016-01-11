COLORS = { black:   "000",
           red:     "f00",
           green:   "0f0",
           yellow:  "ff0",
           blue:    "00f",
           magenta: "f0f",
           cyan:    "0ff",
           white:   "fff" }

a = { water: 'wet', fire: 'hot'}
a = { :water => 'wet', :fire => 'hot'}


class String
  COLORS.each do |color, code|
    define_method "in_#{color}" do
      "<span style=\"color:##{code}\">#{self}</span>"
    end
  end
end

puts "Hello, world!".in_blue
