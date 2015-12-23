<?php
function myAge($birthYear) {                                // defines a function, this one is named "myAge"
  $yearsOld = date('Y') - $birthYear;                       // calculates the age
  return $yearsOld . ' year' . ($yearsOld != 1 ? 's' : ''); // returns the age in a descriptive form
}

echo 'I am currently ' . myAge(1981) . ' old.';               // outputs the text concatenated
                                                              // with the return value of myAge()
                                                              // As the result of this syntax, myAge() is called.
?>

