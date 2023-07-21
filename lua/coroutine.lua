local co = coroutine.create(function()
  coroutine.yield('step 1 done.')
  coroutine.yield('step 2 done.')
  return 'final step done'
end)

print(coroutine.resume(co))
print(coroutine.resume(co))
print(coroutine.resume(co))
print(coroutine.resume(co))


