# name () compound-command [ redirections ]

# or

# function name [()] compound-command [ redirections ]


func ()
{
  echo "This function is running with $# arguments"
}

func a
func a b
func a b c

function another 
{
  echo "Another is running"
}

another

