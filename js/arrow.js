const dragonEvents = [
  {type: 'yawn', value: 40 },
  {type: 'eat', target: 'horse' },
]


const eatTarget = dragonEvents
  .filter(function(event){
    return event.type == 'eat';
  })

  .map(function(event){
    return event.target;
  })

  [0];


const eatTarget2 = dragonEvents
  .filter((event) => { return event.type == 'eat';
  })

  .map((event) => { return event.target;
  })

  [0];

const eatTarget3 = dragonEvents
  .filter(e => e.type == 'eat')
  .map(e => e.target)
  [0];


print('40')


print(eatTarget);
print(eatTarget2);
print(eatTarget3);

//console.log(eatTarget);
//console.log(eatTarget2);



