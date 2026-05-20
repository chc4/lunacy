-- EXPECT: xyz
function fast() local t = { print = print }; t.print('xyz'); end fast()