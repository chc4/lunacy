-- nbody's `advance`: long runs of window ops under register pressure, hot enough
-- to be JIT compiled.
local sqrt = math.sqrt
local floor = math.floor
local function advance(bodies, nbody, dt)
  for i=1,nbody do
    local bi = bodies[i]
    local bix, biy, biz, bimass = bi.x, bi.y, bi.z, bi.mass
    local bivx, bivy, bivz = bi.vx, bi.vy, bi.vz
    for j=i+1,nbody do
      local bj = bodies[j]
      local dx, dy, dz = bix-bj.x, biy-bj.y, biz-bj.z
      local dist2 = dx*dx + dy*dy + dz*dz
      local mag = sqrt(dist2)
      mag = dt / (mag * dist2)
      local bm = bj.mass*mag
      bivx = bivx - (dx * bm)
      bivy = bivy - (dy * bm)
      bivz = bivz - (dz * bm)
      bm = bimass*mag
      bj.vx = bj.vx + (dx * bm)
      bj.vy = bj.vy + (dy * bm)
      bj.vz = bj.vz + (dz * bm)
    end
    bi.vx = bivx
    bi.vy = bivy
    bi.vz = bivz
    bi.x = bix + dt * bivx
    bi.y = biy + dt * bivy
    bi.z = biz + dt * bivz
  end
end


local function body(x, y, z, vx, vy, vz, mass)
  return {x=x, y=y, z=z, vx=vx, vy=vy, vz=vz, mass=mass}
end
local bodies = {
  body(0, 0, 0, 0, 0, 0, 39.47),
  body(4.84, -1.16, -0.10, 0.60, 2.81, -0.02, 0.037),
  body(8.34, 4.12, -0.40, -1.01, 1.82, 0.008, 0.011),
  body(12.89, -15.11, -0.22, 1.08, 0.86, -0.01, 0.0017),
}
for i = 1, 200 do
  advance(bodies, #bodies, 0.01)
end
for i = 1, #bodies do
  local b = bodies[i]
  local x, vy, vz = floor(b.x * 1e9), floor(b.vy * 1e9), floor(b.vz * 1e9)
  print(x, vy, vz)
end
-- EXPECT: 3104605	1124643	-70356
-- EXPECT: 2959570353	1777907823	43532654
-- EXPECT: 5562736626	1234141494	46393225
-- EXPECT: 14912949812	1002449331	-7704959
