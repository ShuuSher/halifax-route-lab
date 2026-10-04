// Browser-compatible routing core. Distances are metres; times are seconds.
function distance(a, b) {
  const rad = Math.PI / 180;
  const h = Math.sin((b.lat - a.lat) * rad / 2) ** 2
    + Math.cos(a.lat * rad) * Math.cos(b.lat * rad)
    * Math.sin((b.lon - a.lon) * rad / 2) ** 2;
  return 12742000 * Math.asin(Math.sqrt(Math.min(1, h)));
}

class Heap {
  items = [];
  push(item) {
    const a = this.items;
    a.push(item);
    let i = a.length - 1;
    while (i > 0) {
      const p = (i - 1) >> 1;
      if (a[p].priority <= item.priority) break;
      a[i] = a[p]; i = p;
    }
    a[i] = item;
  }
  pop() {
    const a = this.items, first = a[0], last = a.pop();
    if (a.length) {
      let i = 0;
      while (2 * i + 1 < a.length) {
        let c = 2 * i + 1;
        if (c + 1 < a.length && a[c + 1].priority < a[c].priority) c++;
        if (a[c].priority >= last.priority) break;
        a[i] = a[c]; i = c;
      }
      a[i] = last;
    }
    return first;
  }
}

function prepareGraph(graph) {
  const nodes = new Map(graph.nodes.map(n => [n.id, n]));
  if (nodes.size !== graph.nodes.length) throw new Error('Duplicate node ID');
  const edges = new Map(), adjacency = new Map(), neighbours = new Map();
  let distanceBound = 1, timeBound = Infinity;
  for (const e of graph.edges) {
    if (edges.has(e.id) || !nodes.has(e.from) || !nodes.has(e.to)
      || !Number.isFinite(e.distance_m) || e.distance_m <= 0
      || !Number.isFinite(e.base_time_s) || e.base_time_s <= 0) {
      throw new Error(`Invalid edge ${e.id}`);
    }
    edges.set(e.id, e);
    if (!adjacency.has(e.from)) adjacency.set(e.from, []);
    adjacency.get(e.from).push(e);
    for (const [a, b] of [[e.from, e.to], [e.to, e.from]]) {
      if (!neighbours.has(a)) neighbours.set(a, new Set());
      neighbours.get(a).add(b);
    }
    const direct = distance(nodes.get(e.from), nodes.get(e.to));
    if (direct > 0) {
      distanceBound = Math.min(distanceBound, e.distance_m / direct);
      timeBound = Math.min(timeBound, e.base_time_s / direct);
    }
  }
  // Conservative bounds preserve admissibility even with rounded source weights.
  const restrictions = new Map();
  for (const r of graph.restrictions ?? []) {
    if (!restrictions.has(r.via)) restrictions.set(r.via, []);
    restrictions.get(r.via).push(r);
  }
  return { nodes, edges, adjacency, neighbours, restrictions,
    distanceBound: distanceBound * (1 - 1e-12),
    timeBound: Number.isFinite(timeBound) ? timeBound * (1 - 1e-12) : 0 };
}

function nearestNode(graph, point) {
  let best = null, metres = Infinity;
  for (const n of graph.nodes.values()) {
    const d = distance(n, point);
    if (d < metres) { best = n.id; metres = d; }
  }
  return { nodeId: best, distanceM: metres };
}

// Select both directions of one physical OSM segment for a closure or slowdown.
function segmentEdges(graph, edgeId) {
  const selected = graph.edges.get(edgeId);
  if (!selected) throw new Error('Unknown segment');
  return [...graph.edges.values()].filter(e => e.osm_way_id === selected.osm_way_id
    && e.segment_index === selected.segment_index).map(e => e.id);
}

function route(graph, start, target, {
  algorithm = 'dijkstra', objective = 'fastest', closedEdges = [],
  slowdowns = {}, intersectionDelayS = 0, intersectionDelays = null, trace = false,
} = {}) {
  if (!['dijkstra', 'astar', 'greedy'].includes(algorithm)) throw new Error('Unknown algorithm');
  if (!['fastest', 'shortest'].includes(objective)) throw new Error('Unknown objective');
  if (!graph.nodes.has(start) || !graph.nodes.has(target)) throw new Error('Unknown endpoint');
  if (!Number.isFinite(intersectionDelayS) || intersectionDelayS < 0) throw new Error('Invalid delay');
  if (intersectionDelays && Object.values(intersectionDelays).some(v => !Number.isFinite(v) || v < 0)) throw new Error('Invalid intersection delay');
  const closed = new Set(closedEdges);
  for (const id of closed) if (!graph.edges.has(id)) throw new Error('Unknown closure edge');
  for (const [id, p] of Object.entries(slowdowns)) {
    if (!graph.edges.has(id) || !Number.isFinite(p) || p < 1 || p > 90) {
      throw new Error('Slowdowns must be 1–90%; use closure for 100%');
    }
  }
  const began = performance.now(), events = [], expanded = [];
  const heuristic = id => distance(graph.nodes.get(id), graph.nodes.get(target))
    * (algorithm === 'greedy' ? 1 : objective === 'shortest' ? graph.distanceBound : graph.timeBound);
  const delay = e => {
    if (e.to === target) return 0;
    const n = graph.nodes.get(e.to);
    if (n.virtual) return 0;
    if (intersectionDelays) return intersectionDelays[n.intersection_type] ?? 0;
    return (graph.neighbours.get(e.to)?.size ?? 0) >= 3 ? intersectionDelayS : 0;
  };
  const travel = e => e.base_time_s / (1 - (slowdowns[e.id] ?? 0) / 100);
  const time = e => travel(e) + delay(e);
  const cost = e => objective === 'shortest' ? e.distance_m : time(e);
  const priority = (id, g) => algorithm === 'dijkstra' ? g
    : algorithm === 'astar' ? g + heuristic(id) : heuristic(id);
  const keyFor = (id, incoming) => graph.restrictions.has(id) ? String(id) + '|' + (incoming?.id ?? 'start') : String(id);
  const startKey = keyFor(start, null);
  const queue = new Heap(), scores = new Map([[startKey, 0]]), previous = new Map(), settled = new Set();
  const uniqueExpanded = new Set();
  let targetKey = null;
  queue.push({ id: start, key: startKey, incoming: null, g: 0, priority: priority(start, 0) });
  if (trace) events.push({ type: 'discover', node: start, g: 0, priority: priority(start, 0) });
  while (queue.items.length) {
    const current = queue.pop();
    if (settled.has(current.key) || current.g !== scores.get(current.key)) continue;
    settled.add(current.key); expanded.push(current.id); uniqueExpanded.add(current.id);
    if (trace) events.push({ type: 'expand', node: current.id, g: current.g });
    if (current.id === target) { targetKey = current.key; break; }
    for (const e of graph.adjacency.get(current.id) ?? []) {
      const nextKey = keyFor(e.to, e);
      if (closed.has(e.id) || settled.has(nextKey)) continue;
      if (current.incoming) {
        const rules = (graph.restrictions.get(current.id) ?? []).filter(r => r.from_way === current.incoming.osm_way_id);
        const matches = r => r.to_way === e.osm_way_id && (!r.type.endsWith('u_turn') || e.to === current.incoming.from);
        const only = rules.filter(r => r.type.startsWith('only_'));
        if (rules.some(r => r.type.startsWith('no_') && matches(r)) || (only.length && !only.some(matches))) continue;
      }
      const next = current.g + cost(e);
      if (next >= (scores.get(nextKey) ?? Infinity)) continue;
      scores.set(nextKey, next); previous.set(nextKey, { edge:e, parent:current.key });
      const rank = priority(e.to, next);
      queue.push({ id: e.to, key:nextKey, incoming:e, g: next, priority: rank });
      if (trace) events.push({ type: 'discover', node: e.to, edge: e.id, g: next, priority: rank });
    }
  }
  const found = targetKey !== null, pathEdges = [];
  if (found) {
    let key = targetKey;
    while (key !== startKey) {
      const entry = previous.get(key); pathEdges.push(entry.edge); key = entry.parent;
    }
    pathEdges.reverse();
  }
  return { found, algorithm, objective, cost: found ? scores.get(targetKey) : null,
    distanceM: found ? pathEdges.reduce((s, e) => s + e.distance_m, 0) : null,
    timeS: found ? pathEdges.reduce((s, e) => s + time(e), 0) : null,
    nodeIds: found ? [start, ...pathEdges.map(e => e.to)] : [],
    legs: pathEdges.map(e => ({ edgeId:e.id, travelS:travel(e), delayS:delay(e) })),
    edgeIds: pathEdges.map(e => e.id), expandedCount: uniqueExpanded.size, expandedStateCount:settled.size,
    expandedNodeIds: expanded, events, runtimeMs: performance.now() - began };
}


function geometryOf(graph, edge) {
  return edge.geometry ?? [graph.nodes.get(edge.from), graph.nodes.get(edge.to)];
}
function segmentId(edge) { return edge.segment_id ?? edge.osm_way_id + ':' + edge.segment_index; }
function pointAlong(points, fraction) {
  const lengths = points.slice(1).map((n,i) => distance(points[i],n));
  const total = lengths.reduce((a,b)=>a+b,0), target = Math.max(0,Math.min(1,fraction))*total;
  let traversed = 0;
  for (let i=0;i<lengths.length;i++) {
    if (traversed+lengths[i] >= target || i===lengths.length-1) {
      const t = lengths[i] ? (target-traversed)/lengths[i] : 0;
      return { lat:points[i].lat+t*(points[i+1].lat-points[i].lat), lon:points[i].lon+t*(points[i+1].lon-points[i].lon) };
    }
    traversed += lengths[i];
  }
  return points[0];
}
function sliceGeometry(points, from, to) {
  const lengths = points.slice(1).map((p,i)=>distance(points[i],p)), total=lengths.reduce((a,b)=>a+b,0);
  let cumulative = 0;
  const interior = [];
  for(let i=1;i<points.length-1;i++) { cumulative+=lengths[i-1]; if(cumulative/total>from && cumulative/total<to) interior.push(points[i]); }
  return [pointAlong(points,from),...interior,pointAlong(points,to)];
}
function snapToRoad(graph, point) {
  let best = null, minimum = Infinity;
  const seen = new Set(), cos = Math.cos(point.lat*Math.PI/180);
  for(const e of graph.edges.values()) {
    if(graph.snapNodes && (!graph.snapNodes.has(e.from)||!graph.snapNodes.has(e.to)))continue;
    const key=segmentId(e); if(seen.has(key)) continue; seen.add(key);
    const points=geometryOf(graph,e), lengths=points.slice(1).map((p,i)=>distance(points[i],p)), total=lengths.reduce((a,b)=>a+b,0);
    let before=0;
    for(let i=0;i<points.length-1;i++) {
      const a=points[i],b=points[i+1], dx=(b.lon-a.lon)*cos,dy=b.lat-a.lat;
      const t=Math.max(0,Math.min(1,((point.lon-a.lon)*cos*dx+(point.lat-a.lat)*dy)/(dx*dx+dy*dy||1)));
      const snapped={lat:a.lat+t*(b.lat-a.lat),lon:a.lon+t*(b.lon-a.lon)}, d=distance(point,snapped);
      if(d<minimum) { minimum=d; best={...snapped,edgeId:e.id,segmentId:key,fraction:(before+t*lengths[i])/total,distanceM:d}; }
      before+=lengths[i];
    }
  }
  if(!best) throw new Error('No roads to snap to');
  return best;
}
// Split only roads holding A/B. Cost and one-way direction are conserved.
function attachEndpoints(base, a, b) {
  const groups=new Map(), nodes=[...base.nodes.values()], endpointIds=[];
  for(const [index,p] of [a,b].entries()) {
    const e=base.edges.get(p.edgeId);
    if(p.fraction<1e-8) { endpointIds[index]=e.from; continue; }
    if(p.fraction>1-1e-8) { endpointIds[index]=e.to; continue; }
    if(!groups.has(p.segmentId)) groups.set(p.segmentId,[]);
    const list=groups.get(p.segmentId), existing=list.find(q=>Math.abs(q.fraction-p.fraction)<1e-8);
    const id=existing?.id ?? ('endpoint-'+index);
    endpointIds[index]=id;
    if(!existing) { list.push({...p,id}); nodes.push({id,lat:p.lat,lon:p.lon,virtual:true,intersection_type:null}); }
  }
  const edges=[];
  for(const e of base.edges.values()) {
    const cuts=groups.get(segmentId(e));
    if(!cuts) { edges.push(e); continue; }
    const canonical=base.edges.get(cuts[0].edgeId);
    const reverse=e.id!==canonical.id;
    const sorted=[{fraction:0,id:e.from},...cuts.map(p=>({...p,fraction:reverse?1-p.fraction:p.fraction})),{fraction:1,id:e.to}].sort((a,b)=>a.fraction-b.fraction);
    for(let i=0;i<sorted.length-1;i++) {
      const from=sorted[i],to=sorted[i+1],portion=to.fraction-from.fraction;
      if(portion<=1e-10) continue;
      edges.push({...e,id:e.id+'@'+i,parent_edge_id:e.id,from:from.id,to:to.id,
        distance_m:e.distance_m*portion,base_time_s:e.base_time_s*portion,geometry:sliceGeometry(geometryOf(base,e),from.fraction,to.fraction)});
    }
  }
  const restrictions=[...base.restrictions.values()].flat();
  return { graph:prepareGraph({nodes,edges,restrictions}),start:endpointIds[0],target:endpointIds[1] };
}



// A physical section owns directed routing edges; it never changes their direction.
function buildSections(graph) {
  const physical=new Map(), incident=new Map();
  for(const edge of graph.edges.values()) {
    const key=segmentId(edge);
    if(!physical.has(key)) physical.set(key,{edge,ids:[]});
    physical.get(key).ids.push(edge.id);
  }
  for(const [key,{edge:e}] of physical) for(const n of new Set([e.from,e.to])) {
    if(!incident.has(n))incident.set(n,[]);incident.get(n).push(key);
  }
  const kind=e=>e.bridge&&e.bridge!=='no'?'bridge':e.tunnel&&e.tunnel!=='no'?'tunnel':e.causeway&&e.causeway!=='no'?'causeway':e.junction==='roundabout'?'roundabout':e.highway?.endsWith('_link')?'ramp':'road';
  const identity=(a,b)=>a.osm_way_id===b.osm_way_id || Boolean((a.structure_name||a.name||a.ref) && (a.structure_name||a.name||a.ref)===(b.structure_name||b.name||b.ref) && a.highway===b.highway);
  const byEdge=new Map(),sections=new Map(),assigned=new Set();
  for(const [key,{edge:first}] of physical) {
    if(assigned.has(key))continue;
    const type=kind(first),keys=[],queue=[key];let length=0;
    while(queue.length) {
      const k=queue.shift();if(assigned.has(k))continue;
      const e=physical.get(k).edge;
      if(kind(e)!==type || (!['roundabout','ramp'].includes(type) && !identity(first,e)))continue;
      if(type==='road' && length && length+e.distance_m>200.001)continue;
      assigned.add(k);keys.push(k);length+=e.distance_m;
      for(const n of [e.from,e.to]) {
        const next=incident.get(n)||[];
        // Structures retain their full connected extent, ordinary roads and ramps stop at junctions.
        if((type==='road'||type==='ramp') && next.length!==2)continue;
        for(const other of next)if(!assigned.has(other))queue.push(other);
      }
    }
    const ids=keys.flatMap(k=>physical.get(k).ids), id=keys.slice().sort().join('|');
    const section={id,type,name:first.structure_name||first.name||first.ref||'Unnamed road',lengthM:length,edgeIds:ids,physicalIds:keys,
      representativeIds:keys.map(k=>physical.get(k).edge.id),anchor:pointAlong(geometryOf(graph,first),.5)};
    sections.set(id,section);for(const eid of ids)byEdge.set(eid,section);
  }
  // Explicit structure names can join separately mapped carriageways of one bridge.
  const named=new Map();
  for(const section of [...sections.values()]) {
    if(!['bridge','tunnel','causeway'].includes(section.type))continue;
    const first=graph.edges.get(section.edgeIds[0]);
    const name=first.structure_name||(/bridge|tunnel|causeway/i.test(first.name||'')?first.name:null);
    if(!name)continue;const key=section.type+':'+name;
    if(!named.has(key)){named.set(key,section);continue;}
    const group=named.get(key);sections.delete(section.id);
    group.edgeIds.push(...section.edgeIds);group.physicalIds.push(...section.physicalIds);group.representativeIds.push(...section.representativeIds);group.lengthM+=section.lengthM;
    for(const id of section.edgeIds)byEdge.set(id,group);
  }
  return {sections,byEdge};
}

function disruptionOptions(graph, disruptions) {
  const closedEdges=new Set(),slowdowns={};
  // Section keys are UI identities, not routing edge IDs. Preserve every
  // directed edge owned by the section, including its reverse where present.
  for(const d of disruptions){
    if(d.suspended)continue;
    for(const id of d.edges){
      if(d.kind==='closure')closedEdges.add(id);
      else if(d.kind==='slowdown')slowdowns[id]=d.percent;
    }
  }
  // Snapped A/B points split base edges. Their fractional children inherit
  // the parent disruption without changing any lengths or travel-time rules.
  for(const e of graph.edges.values()) {
    if(e.parent_edge_id==null)continue;
    if(closedEdges.has(e.parent_edge_id))closedEdges.add(e.id);
    if(Object.hasOwn(slowdowns,e.parent_edge_id))slowdowns[e.id]=slowdowns[e.parent_edge_id];
  }
  // Endpoint attachment can replace a parent entirely; pass only IDs present
  // in this routing graph after transferring its condition to the children.
  for(const id of closedEdges)if(!graph.edges.has(id))closedEdges.delete(id);
  for(const id of Object.keys(slowdowns))if(!graph.edges.has(id))delete slowdowns[id];
  return {closedEdges:[...closedEdges],slowdowns};
}

// Iterative SCCs avoid recursion limits on a larger region. Keep all roads, restrict only snapping.
function connectivity(graph) {
  const reverse=new Map(),visited=new Set(),order=[];
  for(const e of graph.edges.values()){if(!reverse.has(e.to))reverse.set(e.to,[]);reverse.get(e.to).push(e.from);}
  for(const id of graph.nodes.keys()) {
    if(visited.has(id))continue;visited.add(id);const stack=[[id,0]];
    while(stack.length){const top=stack.at(-1),edges=graph.adjacency.get(top[0])||[];
      if(top[1]<edges.length){const to=edges[top[1]++].to;if(!visited.has(to)){visited.add(to);stack.push([to,0]);}}
      else{order.push(top[0]);stack.pop();}
    }
  }
  visited.clear();const components=[];
  for(const id of order.reverse()) {
    if(visited.has(id))continue;const component=new Set(),stack=[id];visited.add(id);
    while(stack.length){const n=stack.pop();component.add(n);for(const p of reverse.get(n)||[])if(!visited.has(p)){visited.add(p);stack.push(p);}}
    components.push(component);
  }
  components.sort((a,b)=>b.size-a.size);
  return {main:components[0]||new Set(),sizes:components.map(c=>c.size)};
}

// Example endpoints only; recorded experiment results are not part of the UI.
const journeys = [
  {label:'West to waterfront',from:{lat:44.6493,lon:-63.599},to:{lat:44.649,lon:-63.574}},
  {label:'Halifax to Dartmouth',from:{lat:44.649,lon:-63.574},to:{lat:44.671,lon:-63.566}},
  {label:'Bedford to waterfront',from:{lat:44.73,lon:-63.661},to:{lat:44.649,lon:-63.574}},
  {label:'Herring Cove to Halifax',from:{lat:44.571,lon:-63.556},to:{lat:44.649,lon:-63.574}},
  {label:'North to southeast',from:{lat:44.664,lon:-63.595},to:{lat:44.641,lon:-63.571}},
];




// Read-only explanation of already calculated results. Never launches a search.
function fullModelHTML({graph,baseGraph,result,baseline,results,start,target,opts}){
  const n=(value,dp=2)=>Number(value).toFixed(dp);
  const card=(title,formula,variables,example,answer)=>`<article><h3>${title}</h3><p class="formula">${formula}</p><p><strong>Variables.</strong> ${variables}</p><p><strong>Worked example.</strong> ${example}</p><p class="worked-result"><strong>Result.</strong> ${answer}</p></article>`;
  const path=result.found?result.edgeIds.map(id=>graph.edges.get(id)):[];
  const parts=[];
  const live=path.length>0;
  const fallbackPoints=[{lat:44.65,lon:-63.58},{lat:44.6505,lon:-63.5798},{lat:44.651,lon:-63.579}];
  const edge=live?path.reduce((a,b)=>geometryOf(graph,a).length>=geometryOf(graph,b).length?a:b):null;
  const points=edge?geometryOf(graph,edge):fallbackPoints;
  const a=start||fallbackPoints[0],b=target||fallbackPoints[2],rad=Math.PI/180;
  const phi1=a.lat*rad,phi2=b.lat*rad,dphi=phi2-phi1,dlambda=(b.lon-a.lon)*rad;
  const h=Math.sin(dphi/2)**2+Math.cos(phi1)*Math.cos(phi2)*Math.sin(dlambda/2)**2;
  parts.push(card('1. Geographic distance: Haversine',
    'a = sin²(Δφ/2) + cos φ₁ cos φ₂ sin²(Δλ/2); d = 2R arcsin(√a)',
    'φ is latitude, λ is longitude (both in radians); Δ means the difference between endpoints. R = 6,371,000 m is the assumed spherical Earth radius; a is dimensionless. Convert degrees using radians = degrees × π/180.',
    `${start&&target?'Current snapped A/B':'Fallback coordinates'}: (${n(a.lat,6)}°, ${n(a.lon,6)}°) and (${n(b.lat,6)}°, ${n(b.lon,6)}°). φ₁ = ${n(phi1,8)}, φ₂ = ${n(phi2,8)}, Δλ = ${n(dlambda,8)} rad; a ≈ ${h.toExponential(6)}. Substitute into 2 × 6,371,000 × arcsin(√a).`,
    `${n(distance(a,b))} m of direct spherical distance, not driving distance. Rounded substitutions are shown; calculations use full precision.`));
  const lengths=points.slice(1).map((point,i)=>distance(points[i],point)),polyline=lengths.reduce((s,v)=>s+v,0);
  const sum=(values)=>values.length<=5?values.map(v=>n(v)).join(' + '):values.slice(0,3).map(v=>n(v)).join(' + ')+` + … + ${n(values.at(-1))} (${values.length} terms)`;
  parts.push(card('2. Curved roads and polylines','dₑ = ∑ᵢ₌₁ᵐ H(qᵢ₋₁, qᵢ)',
    'q₀,…,qₘ are the ordered geometry points of one road edge; H is Haversine distance in metres; m is the number of straight pieces.',
    `${live?'Current route: the edge with the most geometry points':'Fallback three-point curved road'} has ${points.length} points. Sum ${sum(lengths)} m.`,
    `${n(polyline)} m from geometry.${edge?` Stored routing length: ${n(edge.distance_m)} m. Small differences can arise from imported rounding and fractional endpoint splitting.`:''}`));
  parts.push(card('3. Weighted directed graph','G = (V, E), w(e) = dₑ or t′ₑ + I',
    'V is the set of intersections/road points; E is the set of allowed directed car-road edges. Weights are metres for Shortest, seconds for Fastest. A two-way road can have two directed edges; a one-way road cannot be traversed backwards.',
    `Current loaded road graph: |V| = ${baseGraph.nodes.size.toLocaleString()}, |E| = ${baseGraph.edges.size.toLocaleString()}. Snapped A/B may split edges in the temporary routing graph.`,
    `${graph.nodes.size.toLocaleString()} vertices and ${graph.edges.size.toLocaleString()} directed edges in the current routing graph (counts, not distance units).`));
  parts.push(card('4. Shortest-route objective','C(P) = ∑ₑ∈P dₑ',
    'P is a candidate directed path and dₑ is the stored length of edge e in metres. Shortest minimizes this sum over permitted paths.',
    result.found?`Current selected path: ${live?sum(path.map(e=>e.distance_m)):'0 (empty path; A and B coincide)'} m. This illustrates the distance objective even when Fastest or Greedy is selected.`:'Fallback path: 100 + 150 + 250 m. No active path is available.',
    result.found?`${n(result.distanceM)} m = ${n(result.distanceM/1000,3)} km. This selected path is not necessarily the shortest path.`:'500.00 m = 0.500 km (fallback).'));
  const d=edge?.distance_m??200,v=edge?.speed_kmh??40,t=3.6*d/v;
  parts.push(card('5. Basic edge travel time','tₑ = 3.6dₑ / vₑ',
    'dₑ is distance in metres, vₑ is speed in km/h and tₑ is time in seconds. The conversion factor is 3,600 s/h ÷ 1,000 m/km. OSM speed limits are used where available, otherwise road-type assumptions.',
    `${live?'Current route edge':'Fallback edge'}: 3.6 × ${n(d)} / ${n(v)}.`,
    `${n(t)} s.${edge?` Stored basic routing time: ${n(edge.base_time_s)} s (imported values may be rounded).`:''}`));
  const slowIds=Object.keys(opts.slowdowns||{});
  const slowEdge=path.find(e=>Object.hasOwn(opts.slowdowns||{},e.id))||graph.edges.get(slowIds[0]);
  const p=slowEdge?opts.slowdowns[slowEdge.id]:50,sv=slowEdge?.speed_kmh??40,st=slowEdge?.base_time_s??18;
  const slowLabel=slowEdge?(path.includes(slowEdge)?'Current route slowed edge':'Active slowed edge off the current route'):'Fallback only: no active slowdown';
  parts.push(card('6. Lane slowdown: speed and time','v′ = v(1 − p/100); t′ = t / (1 − p/100)',
    'p is the percentage speed reduction (1–90%); v and v′ are km/h; t and t′ are the edge travel times in seconds, excluding intersection delay. This affects every directed edge in the selected section, not only a portion of a lane.',
    `${slowLabel}: p = ${n(p)}%. Speed: ${n(sv)} × (1 − ${n(p)}/100). Time: ${n(st)} / (1 − ${n(p)}/100).`,
    `v′ = ${n(sv*(1-p/100))} km/h; t′ = ${n(st/(1-p/100))} s.`));
  const travel=result.legs.reduce((s,l)=>s+l.travelS,0),delay=result.legs.reduce((s,l)=>s+l.delayS,0);
  parts.push(card('7. Fastest-route objective','T(P) = ∑ₑ∈P 3.6dₑ / v′ₑ + ∑ⱼ Iⱼ',
    'v′ₑ includes any active slowdown. Iⱼ is the assumed delay in seconds at an eligible junction arrival. Fastest minimizes total modelled time, not distance.',
    result.found?`Current selected route: sum of adjusted road travel = ${n(travel)} s; sum of junction delays = ${n(delay)} s. Add ${n(travel)} + ${n(delay)}.`:'Fallback: 120 s of road travel + 15 s of junction delays. The current endpoints have no available route.',
    result.found?`${n(result.timeS)} s = ${n(result.timeS/60)} min. This is the selected path’s time; Greedy or the Shortest objective need not minimize it.`:'135.00 s = 2.25 min (fallback).'));
  parts.push(card('8. Basic versus Intersection Delays','TBasic(P) = ∑ t′ₑ; TDelays(P) = ∑ t′ₑ + ∑ Iⱼ',
    'Basic sets Iⱼ = 0. Intersection Delays uses the user’s ordinary/stop/signal assumptions. No delay is added at a virtual endpoint or the destination. Comparisons here hold the path fixed; changing model may select a different path.',
    `Current model: ${opts.intersectionDelays?'Intersection Delays':'Basic'}. `+(result.found?`For this fixed path, ${n(travel)} s road travel + ${n(delay)} s currently enabled delays.`:'Fallback fixed path: 120 s road travel plus 3 junctions × 5 s assumed delay.'),
    result.found?`${n(travel)} s without junction delays; ${n(result.timeS)} s with the current settings.`:'Basic 120.00 s; Intersection Delays 135.00 s (illustrative assumptions, not measured traffic).'));
  parts.push(card('9. Full closures','Eavailable = E ∖ Eclosed',
    'Eclosed contains all directed edge IDs belonging to active closed sections, including fractional endpoint edges. A closure disables traversal; it is not modelled by dividing by zero speed. Suspended markers are excluded until dropped.',
    `Current routing graph: ${graph.edges.size.toLocaleString()} edges − ${opts.closedEdges.length.toLocaleString()} disabled edges.`,
    `${(graph.edges.size-opts.closedEdges.length).toLocaleString()} available directed edges (count).${!result.found?' No Route Available for the current endpoints.':''}`));
  const first=path[0],unit=opts.objective==='shortest'?'m':'s';
  const g=first?(opts.objective==='shortest'?first.distance_m:result.legs[0].travelS+result.legs[0].delayS):20;
  const remaining=first?distance(graph.nodes.get(first.to),target):100;
  const bound=opts.objective==='shortest'?graph.distanceBound:graph.timeBound;
  const heuristic=first?remaining*bound:10;
  const searchExample=first?'Current route example, after its first edge':'Fallback search state';
  parts.push(card('10. Dijkstra priority','f = g',
    'g is accumulated path cost; f is the queue priority. Both use metres under Shortest and seconds under Fastest. Dijkstra expands the smallest accumulated cost.',
    `${searchExample}: g = ${n(g)} ${unit}.`,`${n(g)} ${unit} priority.`));
  parts.push(card('11. A* priority','f = g + h',
    'h is an optimistic remaining cost in the same units as g. Here it is direct Haversine distance × a conservative graph-wide cost-per-metre bound. Non-negative slowdowns and delays do not invalidate this lower bound.',
    `${searchExample}: ${first?`h = ${n(remaining)} m × ${n(bound,6)} ${opts.objective==='shortest'?'m/m':'s/m'} = ${n(heuristic)} ${unit}. `:''}f = ${n(g)} + ${n(heuristic)}.`,
    `${n(g+heuristic)} ${unit} priority. A* minimizes the selected cost with this admissible bound.`));
  parts.push(card('12. Greedy Best-First priority','f = h',
    'Greedy ranks only the remaining direct distance and ignores g. In this simulator its h is Haversine distance in metres, even under Fastest. Its returned route still has a distance and time but may be suboptimal.',
    `${searchExample}: h = ${n(remaining)} m; accumulated cost does not enter the priority.`,`${n(remaining)} m priority.`));
  const valid=result.found&&baseline.found&&baseline.cost>0;
  parts.push(card('13. Percentage change from baseline','Δ% = 100(Ccurrent − Cbaseline) / Cbaseline',
    'Both costs use the selected objective: metres for Shortest or seconds for Fastest. Baseline is Dijkstra with the same A/B, no disruptions and Basic delays. A zero baseline makes the percentage undefined.',
    valid?`Current route: 100 × (${n(result.cost)} − ${n(baseline.cost)}) / ${n(baseline.cost)}; costs in ${unit}.`:'Fallback: 100 × (150 − 120) / 120, using seconds. A non-zero live baseline and an available route are needed.',
    valid?`${n(100*(result.cost-baseline.cost)/baseline.cost)}%.`:'25.00% increase (fallback; not a live route result).'));
  const nd=results.dijkstra?.expandedCount,na=results.astar?.expandedCount,compared=nd>0&&na!==undefined;
  parts.push(card('14. A* reduction in vertices explored','Reduction = 100(ND − NA) / ND',
    'ND and NA are unique vertices expanded by Dijkstra and A* under identical endpoints, objective and conditions. This is a count comparison, not a guaranteed runtime improvement. Negative values mean A* expanded more.',
    compared?`Current comparison: 100 × (${nd} − ${na}) / ${nd}.`:'Fallback: Dijkstra 100 vertices, A* 60; 100 × (100 − 60) / 100. Use Compare Algorithms for live values; opening this explanation does not run extra searches.',
    compared?`${n(100*(nd-na)/nd)}% reduction.`:'40.00% reduction (fallback).'));
  parts.push(card('15. Controlled route-switch threshold','T₁(r) = u + s/(1 − r); r* = 1 − s/(T₂ − u)',
    'r = p/100 is a fractional speed reduction; u is unaffected time on route 1; s is its affected section’s original time; T₂ is the time of a fixed avoiding route. All times are seconds. Equate T₁(r*) = T₂ and rearrange. Require T₂ > u and 0 ≤ r* < 1; the simulator permits slowdowns up to r = 0.90.',
    'Controlled fallback, not a prediction for the active map: u = 60 s, s = 30 s, T₂ = 120 s. T₁(r) = 60 + 30/(1 − r). Thus r* = 1 − 30/(120 − 60). At the threshold: 60 + 30/0.5 = 120.',
    'r* = 0.50 = 50% reduction; both routes take 120.00 s = 2.00 min. At 25%, T₁ = 100 s; at 75%, T₁ = 180 s. This assumes fixed paths, unchanged delays and an unaffected alternative; other paths may switch earlier.'));
  parts.push(card('16. Turn restrictions and search state','Search state = (current vertex, incoming edge)',
    'A permitted outgoing edge can depend on how the car entered a junction. At restricted junctions, reaching the same vertex by two incoming roads may create two distinct search states.',
    'Controlled example: arriving at junction J along edge a prohibits J → K, but arriving along edge b permits it. The search must keep (J, a) and (J, b) separate.',
    '1 junction, 2 arrival states, and different legal onward choices (counts). Unique vertices explored and total search states are therefore not interchangeable.'));
  return '<p class="hint">Worked examples update with the last calculated route. During a drag, values remain those of the last completed calculation. Fallback examples are explicitly labelled. Displayed values are rounded; routing uses stored precision.</p>'+parts.join('');
}




const projectionCache=new WeakMap();
function projectPoint(n) { let point=projectionCache.get(n);if(!point){point=[(n.lon+63.5825)*79300,-(n.lat-44.6515)*111195];projectionCache.set(n,point);}return point; }
const geometryCache=new WeakMap();
function cachedGeometry(graph,edge) {
  if(geometryCache.has(edge))return geometryCache.get(edge);
  const points=geometryOf(graph,edge),projected=points.map(projectPoint),lengths=points.slice(1).map((n,i)=>distance(points[i],n));
  const total=lengths.reduce((a,b)=>a+b,0),xs=projected.map(p=>p[0]),ys=projected.map(p=>p[1]);
  const value={points,projected,lengths,total,minX:Math.min(...xs),maxX:Math.max(...xs),minY:Math.min(...ys),maxY:Math.max(...ys),
    west:Math.min(...points.map(p=>p.lon)),east:Math.max(...points.map(p=>p.lon)),south:Math.min(...points.map(p=>p.lat)),north:Math.max(...points.map(p=>p.lat))};
  geometryCache.set(edge,value);return value;
}
function cachedPointAlong(geometry,fraction) {
  const {points,lengths,total}=geometry,target=Math.max(0,Math.min(1,fraction))*total;let before=0;
  for(let i=0;i<lengths.length;i++){
    if(before+lengths[i]>=target||i===lengths.length-1){const t=lengths[i]?(target-before)/lengths[i]:0;return {lat:points[i].lat+t*(points[i+1].lat-points[i].lat),lon:points[i].lon+t*(points[i+1].lon-points[i].lon)};}
    before+=lengths[i];
  }
  return points[0];
}
function intersects(a,b){return a.minX<=b.maxX&&a.maxX>=b.minX&&a.minY<=b.maxY&&a.maxY>=b.minY;}
function geometryVisible(geometry,bounds){return intersects(geometry,bounds);}
function buildTree(items) {
  const box={minX:Infinity,minY:Infinity,maxX:-Infinity,maxY:-Infinity,west:Infinity,east:-Infinity,south:Infinity,north:-Infinity};
  for(const {geometry:g} of items)for(const key of Object.keys(box))box[key]=['minX','minY','west','south'].includes(key)?Math.min(box[key],g[key]):Math.max(box[key],g[key]);
  if(items.length<=12)return {...box,items};
  const axis=box.maxX-box.minX>box.maxY-box.minY?'X':'Y';
  items.sort((a,b)=>(a.geometry['min'+axis]+a.geometry['max'+axis])-(b.geometry['min'+axis]+b.geometry['max'+axis]));
  const middle=items.length>>1;return {...box,left:buildTree(items.slice(0,middle)),right:buildTree(items.slice(middle))};
}
// Conservative spherical lower bound to a latitude/longitude rectangle.
function lowerBound(point,box){
  const latGap=Math.max(box.south-point.lat,point.lat-box.north,0),lonGap=Math.max(box.west-point.lon,point.lon-box.east,0),rad=Math.PI/180;
  if(Math.abs(point.lon-box.west)>180||Math.abs(point.lon-box.east)>180)return 0;
  const cosine=Math.max(0,Math.cos(point.lat*rad))*Math.max(0,Math.min(Math.cos(box.south*rad),Math.cos(box.north*rad)));
  return 12742000*Math.asin(Math.sqrt(Math.min(1,Math.sin(latGap*rad/2)**2+cosine*Math.sin(lonGap*rad/2)**2)))*(1-1e-12);
}
class RoadSpatialIndex {
  constructor(graph){
    this.graph=graph;this.records=[];this.byEdge=new Map();const bySegment=new Map();
    for(const edge of graph.edges.values()){
      const key=segmentId(edge);let record=bySegment.get(key);
      if(!record){const geometry=cachedGeometry(graph,edge);record={edge,geometry,order:this.records.length,directed:[],midpoint:cachedPointAlong(geometry,.5)};this.records.push(record);bySegment.set(key,record);}
      record.directed.push(edge);this.byEdge.set(edge.id,record);
    }
    this.tree=buildTree([...this.records]);this.lastCandidates=0;
  }
  query(bounds){const found=[],stack=[this.tree];
    while(stack.length){const node=stack.pop();if(!intersects(node,bounds))continue;if(node.items){for(const item of node.items)if(intersects(item.geometry,bounds))found.push(item);}else stack.push(node.right,node.left);}
    return found.sort((a,b)=>a.order-b.order);
  }
  snap(point,snapNodes=this.graph.snapNodes){
    let best=null,minimum=Infinity,bestOrder=Infinity;this.lastCandidates=0;
    const cos=Math.cos(point.lat*Math.PI/180),stack=[this.tree];
    while(stack.length){const node=stack.pop();if(lowerBound(point,node)>minimum+1e-8)continue;
      if(!node.items){const l=lowerBound(point,node.left),r=lowerBound(point,node.right);if(l<r)stack.push(node.right,node.left);else stack.push(node.left,node.right);continue;}
      for(const record of node.items){const e=record.edge;if(snapNodes&&(!snapNodes.has(e.from)||!snapNodes.has(e.to)))continue;
        if(lowerBound(point,record.geometry)>minimum+1e-8)continue;this.lastCandidates++;
        const {points,lengths,total}=record.geometry;let before=0;
        for(let i=0;i<points.length-1;i++){
          const a=points[i],b=points[i+1],dx=(b.lon-a.lon)*cos,dy=b.lat-a.lat;
          const t=Math.max(0,Math.min(1,((point.lon-a.lon)*cos*dx+(point.lat-a.lat)*dy)/(dx*dx+dy*dy||1)));
          const snapped={lat:a.lat+t*(b.lat-a.lat),lon:a.lon+t*(b.lon-a.lon)},d=distance(point,snapped);
          if(d<minimum||(d===minimum&&record.order<bestOrder)){minimum=d;bestOrder=record.order;best={...snapped,edgeId:e.id,segmentId:segmentId(e),fraction:(before+t*lengths[i])/total,distanceM:d};}
          before+=lengths[i];
        }
      }
    }
    if(!best)throw new Error('No roads to snap to');return best;
  }
  hit(x,y,radius){
    const records=this.query({minX:x-radius,maxX:x+radius,minY:y-radius,maxY:y+radius});let best=null,min=radius;this.lastCandidates=records.length;
    for(const record of records){const points=record.geometry.projected;
      for(let i=0;i<points.length-1;i++){const a=points[i],b=points[i+1],dx=b[0]-a[0],dy=b[1]-a[1],t=Math.max(0,Math.min(1,((x-a[0])*dx+(y-a[1])*dy)/(dx*dx+dy*dy||1))),d=Math.hypot(x-a[0]-t*dx,y-a[1]-t*dy);if(d<min){min=d;best=record.edge.id;}}
    }
    return best;
  }
}




// Ephemeral computation cache only; no saved user scenarios or browser storage.
class RouteSession {
  constructor(base){this.base=base;this.cache=new Map();this.stats={searches:0,hits:0,attachments:0};}
  endpoints(a,b){
    const key=JSON.stringify([a,b].map(p=>[p.edgeId,p.fraction,p.lat,p.lon]));
    if(key!==this.endpointKey){this.attached=attachEndpoints(this.base,a,b);this.endpointKey=key;this.cache.clear();this.stats.attachments++;}
    return this.attached;
  }
  get(options={}){
    const {algorithm='dijkstra',objective='fastest',trace=false,closedEdges=[],slowdowns={},intersectionDelays=null}=options;
    const typedDelays=intersectionDelays&&(Object.values(intersectionDelays).some(Boolean)||(options.intersectionDelayS??0)!==0)?intersectionDelays:null;
    const key=JSON.stringify([algorithm,objective,closedEdges,slowdowns,typedDelays,options.intersectionDelayS??0]);
    const cached=this.cache.get(key);
    if(cached&&(!trace||cached.traced)){this.stats.hits++;return cached.result;}
    const {graph,start,target}=this.attached,result=route(graph,start,target,{...options,algorithm,objective,trace});this.stats.searches++;
    this.cache.set(key,{result,traced:trace});
    if(this.cache.size>24)this.cache.delete(this.cache.keys().next().value);
    return result;
  }
}

const $ = id => document.getElementById(id);
const names = { dijkstra: 'Dijkstra', astar: 'A*', greedy: 'Greedy' };
const traySlots=Object.fromEntries(['25','50','75','custom','closure'].flatMap(group=>[1,2,3].map(number=>[
  group==='closure'?'closure'+number:'slowdown'+group+'-'+number,
  {group,number,kind:group==='closure'?'closure':'slowdown',percent:['25','50','75'].includes(group)?Number(group):null}
])));
const slotLabel=slot=>{const s=traySlots[slot];return (s.group==='closure'?'Closure':s.group==='custom'?'Custom':s.group+'%')+' '+s.number;};
let samples = [
  [{ lat: 44.6493, lon: -63.5990 }, { lat: 44.6490, lon: -63.5740 }],
  [{ lat: 44.664, lon: -63.595 }, { lat: 44.641, lon: -63.571 }],
  [{ lat: 44.640, lon: -63.580 }, { lat: 44.663, lon: -63.590 }],
  [{ lat: 44.638, lon: -63.583 }, { lat: 44.674, lon: -63.625 }],
];
const state = { algorithm: 'dijkstra', objective: 'fastest', view: 'gps', disruptions: [], selected: null,
  placing: null, delays: null, playing: false, playIndex: 0, results: {}, start: null, target: null,
  comparison:'algorithms', optimalRoutes:{}, car:null, driving:false, slot:null, editing:null, preview:null };
const canvas = $('map'), ctx = canvas.getContext('2d');
let graph, baseGraph, sectionIndex, roadIndex, routeSession, raw, width = 800, height = 470, scale = 1, zoom = 1, pan = [0, 0], drag = null, frame = 0, driveFrame = 0;
const xy = projectPoint;
let algorithmComparisonRequested=false,algorithmPanelVisible=false,drawFrame=0,pendingPointer=null,inFrame=false,currentBounds,visibleKey='',visibleRoads=[];
let searchResult=null,searchIndex=0,searchExplored=new Set(),searchFrontier=new Set();
let modelContext=null;
function updateFullModel(){if(modelContext&&$('full-model').open)$('full-model-content').innerHTML=fullModelHTML(modelContext);}
let backgroundPaths=null,backgroundRaster=null,backgroundVersion=0,visiblePan=[0,0];
let roadMovement=false,roadIdleTimer=0;
function roadMotion(){roadMovement=true;clearTimeout(roadIdleTimer);roadIdleTimer=setTimeout(endRoadMotion,180);}
function endRoadMotion(){clearTimeout(roadIdleTimer);if(roadMovement){roadMovement=false;draw();}}
const sectionGeometry=new Map(),perfStats={frames:0,visibleRoads:0,roadStrokes:0,backgroundRoadStrokes:0,pointerUpdates:0,lastFrameMs:0};
function queuePointer(callback){pendingPointer=callback;draw();}
function flushPointer(){const callback=pendingPointer;pendingPointer=null;if(callback){perfStats.pointerUpdates++;callback();}}
function flushDraw(){if(drawFrame)cancelAnimationFrame(drawFrame);drawFrame=0;inFrame=true;flushPointer();renderMap();inFrame=false;}
function draw(){if(!drawFrame&&!inFrame)drawFrame=requestAnimationFrame(flushDraw);}
function worldScreen(p){return [width/2+pan[0]+p[0]*scale*zoom,height/2+pan[1]+p[1]*scale*zoom];}
function viewportBounds(buffer=48){const f=scale*zoom;return {minX:(-buffer-width/2-pan[0])/f,maxX:(width+buffer-width/2-pan[0])/f,minY:(-buffer-height/2-pan[1])/f,maxY:(height+buffer-height/2-pan[1])/f};}
const screen = n => { const [x, y] = xy(n); return [width / 2 + pan[0] + x * scale * zoom, height / 2 + pan[1] + y * scale * zoom]; };
const geo = (x, y) => ({ lon: (x - width / 2 - pan[0]) / (scale * zoom * 79300) - 63.5825,
  lat: -(y - height / 2 - pan[1]) / (scale * zoom * 111195) + 44.6515 });
const formatM = n => n === null ? '—' : n < 1000 ? Math.round(n) + ' m' : (n / 1000).toFixed(2) + ' km';
const minuteSeconds = n => Math.floor(Math.round(n)/60) + 'm ' + (Math.round(n)%60) + 's';
const formatT = n => n === null ? '—' : (n / 60).toFixed(2) + ' min (' + minuteSeconds(n) + ')';
function status(text) { $('status').textContent = text; }
function options() {
  return { objective:state.objective, ...disruptionOptions(graph,state.disruptions), intersectionDelays:state.delays };
}
function stop() { state.playing = false; cancelAnimationFrame(frame); $('play').textContent = '▶ Replay search'; }
function stopDrive() { cancelAnimationFrame(driveFrame); state.driving=false; state.car=null; $('drive').textContent='▶ Start Drive';$('drive').disabled=!state.results[state.algorithm]?.found; }
function calculate(presentationOnly=false) {
  if (!baseGraph || !state.start || !state.target) return;
  if(!presentationOnly){stop();stopDrive();}
  const attached=routeSession.endpoints(state.start,state.target);
  graph=attached.graph; state.start.nodeId=attached.start; state.target.nodeId=attached.target;
  const opts = options();
  state.results={};
  const compareAll=state.comparison==='algorithms'&&(algorithmComparisonRequested||algorithmPanelVisible);
  state.results[state.algorithm]=routeSession.get({...opts,algorithm:state.algorithm,trace:true});
  if(compareAll)for(const algorithm of Object.keys(names))if(algorithm!==state.algorithm)state.results[algorithm]=routeSession.get({...opts,algorithm});
  const result = state.results[state.algorithm];
  $('route-segment').replaceChildren(new Option('Select a segment…', ''));
  const parents=[...new Set(result.edgeIds.map(id=>graph.edges.get(id).parent_edge_id ?? id))];
  for (const [i, id] of parents.entries()) {
    const e = baseGraph.edges.get(id);
    $('route-segment').append(new Option((i + 1) + '. ' + (e.name || 'Unnamed road') + ' · ' + formatM(e.distance_m), id));
  }
  $('route-segment').value = parents.includes(state.selected) ? state.selected : '';
  if(!presentationOnly)state.playIndex = result.events.length;
  $('progress').max = result.events.length || 1; $('progress').value = state.playIndex;
  $('play').disabled = result.events.length === 0;
  $('drive').disabled = state.driving || !result.found || result.timeS<=0;
  $('distance').textContent = formatM(result.distanceM);
  $('time').replaceChildren(document.createTextNode(result.found?(result.timeS/60).toFixed(2)+' min':'—'));
  if(result.found) { const small=document.createElement('small');small.textContent=minuteSeconds(result.timeS);$('time').append(small); }
  $('expanded').textContent = result.expandedCount.toLocaleString();
  const base = routeSession.get({objective:state.objective});
  const optimal=state.results.dijkstra??routeSession.get({...opts,algorithm:'dijkstra'});
  const changed=optimal.found!==base.found || (optimal.found && optimal.edgeIds.join('|')!==base.edgeIds.join('|'));
  $('result-algorithm').textContent=names[state.algorithm];
  $('result-disruptions').textContent=state.disruptions.filter(d=>d.kind==='slowdown').length+' slowdowns · '+state.disruptions.filter(d=>d.kind==='closure').length+' closures';
  $('result-model').textContent=state.delays?'Intersection Delays':'Basic';
  $('result-change').textContent=!base.found?'Baseline unavailable':!optimal.found?'No route under these conditions':changed?'Optimal route changed':'Optimal route unchanged';
  $('result-change').title='Compares Dijkstra paths under the current conditions with the Basic, undisrupted optimum. Equal-cost alternative paths may exist.';
  $('change').textContent = result.found && base.found && base.cost > 0 ? ((result.cost / base.cost - 1) * 100).toFixed(1) + '%' : '—';
  $('change-label').textContent=state.objective==='fastest'?'Time vs baseline':'Distance vs baseline';
  $('change').title = base.found && base.cost === 0 ? 'Percentage change is undefined because the baseline cost is zero.' : 'Selected route versus undisrupted Dijkstra: same endpoints and objective, Basic model.';
  $('a-label').textContent = pointLabel(state.start); $('b-label').textContent = pointLabel(state.target);
  $('priority').textContent = { dijkstra: 'Dijkstra: g', astar: 'A*: g + h', greedy: 'Greedy: h' }[state.algorithm];
  $('results').replaceChildren();
  const optimum = optimal;
  for (const algorithm of Object.keys(names)) {
    const r=state.results[algorithm];
    const tr = document.createElement('tr'); tr.className = algorithm === state.algorithm ? 'selected' : '';
    const td = document.createElement('td'), button = document.createElement('button');
    button.textContent = names[algorithm]; button.onclick = () => { $('algorithm').value = algorithm; state.algorithm = algorithm; calculate(); };
    td.append(button); tr.append(td);
    if(!r){for(const text of ['—','—','—','—','On comparison']){const cell=document.createElement('td');cell.textContent=text;tr.append(cell);}$('results').append(tr);continue;}
    const extra = r.found && optimum.found && optimum.cost > 0 ? (100 * (r.cost / optimum.cost - 1)).toFixed(1) + '%' : '—';
    for (const value of [formatM(r.distanceM), formatT(r.timeS), r.expandedCount.toLocaleString(), extra, r.found&&optimum.found?(r.edgeIds.join('|')===optimum.edgeIds.join('|')?'Yes':'No'):'—']) { const cell = document.createElement('td'); cell.textContent = value; tr.append(cell); }
    $('results').append(tr);
  }
  $('route-comparison').replaceChildren();
  state.optimalRoutes={};
  if(state.comparison==='routes')for(const objective of ['fastest','shortest']) {
    const r=routeSession.get({...opts,objective,algorithm:'dijkstra'}), tr=document.createElement('tr');
    state.optimalRoutes[objective]=r;
    tr.className=objective===state.objective?'selected':'';
    const td=document.createElement('td'),button=document.createElement('button');button.textContent=objective==='fastest'?'Fastest':'Shortest';
    button.onclick=()=>{state.objective=objective;state.algorithm='dijkstra';$('objective').value=objective;$('algorithm').value='dijkstra';calculate();};
    td.append(button);tr.append(td);
    for(const value of [formatM(r.distanceM),formatT(r.timeS),r.found?r.edgeIds.length:'—']){const cell=document.createElement('td');cell.textContent=value;tr.append(cell);}
    $('route-comparison').append(tr);
  }
  const d=state.results.dijkstra?.expandedCount,a=state.results.astar?.expandedCount;
  $('search-reduction').textContent=compareAll?'In this experiment, A* expanded '+(d?100*(d-a)/d:0).toFixed(1)+'% fewer unique vertices than Dijkstra. Turn-aware searches may revisit a vertex with a different incoming road.':'All three algorithms run when this comparison is shown or selected.';
  status(result.found ? 'Route updated. A snapped ' + Math.round(state.start.distanceM) + ' m; B snapped ' + Math.round(state.target.distanceM) + ' m. Disruptions remain when you move endpoints.'
    : 'No Route Available. Move A/B or remove a closure. Disconnected roads and direction restrictions in the model can cause this.');
  modelContext={graph,baseGraph,result,baseline:base,results:state.results,start:state.start,target:state.target,opts};
  updateFullModel();roadMath(); draw();
}
function pointLabel(p) { return p.lat.toFixed(4) + ', ' + p.lon.toFixed(4); }
function setSample(index) { const [a, b] = samples[index]; state.start = roadIndex.snap(a); state.target = roadIndex.snap(b); state.selected = null; selectRoad(null); calculate(); fitRoute(); }
function roadMath() {
  $('road-math').hidden=!$('road-details').checked;
  const e=baseGraph?.edges.get(state.selected);
  if(!e){$('road-math').textContent='Select a road to see its distance, speed source and travel-time calculation.';return;}
  const section=sectionIndex.byEdge.get(e.id),disruption=state.disruptions.find(d=>d.key===section.id),p=disruption?.kind==='slowdown'?disruption.percent:0;
  const v=e.speed_kmh*(1-p/100),t=3.6*e.distance_m/v;
  const representatives=section.representativeIds.map(id=>baseGraph.edges.get(id)),speeds=[...new Set(representatives.map(e=>e.speed_kmh))].sort((a,b)=>a-b);
  const sectionTime=representatives.reduce((sum,e)=>sum+e.base_time_s,0);
  $('road-math').textContent=section.name+' · '+section.type+' section · '+formatM(section.lengthM)+' · '+section.edgeIds.length+' directed edges'+
    '\nSelected edge: '+formatM(e.distance_m)+'; '+e.speed_kmh+' km/h · '+(e.speed_source==='osm_maxspeed'?'OSM tag':'road-type assumption')+
    '\nBasic time: 3.6 × '+e.distance_m.toFixed(2)+' / '+e.speed_kmh+' = '+e.base_time_s.toFixed(2)+' s'+
    (disruption?.kind==='closure'?'\nRoad Closed: all directed edges in this section are disabled.':'\nSpeed reduction: '+p+'%. Adjusted edge speed: '+v.toFixed(2)+' km/h; adjusted edge time: '+t.toFixed(2)+' s')+
    '\nSection reference speeds: '+speeds.join(', ')+' km/h → '+speeds.map(v=>(v*(1-p/100)).toFixed(1)).join(', ')+' km/h.'+
    '\nSection reference time: '+sectionTime.toFixed(2)+' s → '+(sectionTime/(1-p/100)).toFixed(2)+' s (one representative direction per physical piece; not a complete itinerary).'+
    '\nSection speed sources: '+[...new Set(representatives.map(e=>e.speed_source==='osm_maxspeed'?'OSM tags':'road-type assumptions'))].join(' and ')+'.'+
    '\nJunction delays are separate. A/B can use a fraction of an edge. Both available directions of the section are affected.';

}
function fitPoints(points) {
  endRoadMotion();
  const coords=points.map(xy),xs=coords.map(p=>p[0]),ys=coords.map(p=>p[1]);
  const xmin=Math.min(...xs),xmax=Math.max(...xs),ymin=Math.min(...ys),ymax=Math.max(...ys);
  const factor=Math.min((width-140)/Math.max(600,xmax-xmin),(height-140)/Math.max(600,ymax-ymin));
  zoom=Math.max(.025,Math.min(22,factor/scale));pan=[-(xmin+xmax)/2*scale*zoom,-(ymin+ymax)/2*scale*zoom];draw();
}
function fitRoute(){const r=state.results[state.algorithm];fitPoints(r?.found&&r.edgeIds.length?r.edgeIds.flatMap(id=>geometryOf(graph,graph.edges.get(id))):[state.start,state.target]);}
function wholeArea(){const b=raw.metadata.bbox_south_west_north_east;fitPoints([{lat:b[0],lon:b[1]},{lat:b[2],lon:b[3]}]);}
function line(e,color,lineWidth) {
  if(!e)return;const geometry=cachedGeometry(graph,e);if(!geometryVisible(geometry,currentBounds))return;
  const points=geometry.projected;ctx.beginPath();ctx.moveTo(...worldScreen(points[0]));
  for(let i=1;i<points.length;i++)ctx.lineTo(...worldScreen(points[i]));
  ctx.strokeStyle=color;ctx.lineWidth=lineWidth;ctx.stroke();perfStats.roadStrokes++;
}
function cacheBackgroundPaths(){
  const normal=new Path2D(),major=new Path2D();
  for(const record of visibleRoads){
    if(!record.path){const path=new Path2D(),points=record.geometry.projected;path.moveTo(...points[0]);for(let i=1;i<points.length;i++)path.lineTo(...points[i]);record.path=path;}
    (['primary','secondary'].includes(record.edge.highway)?major:normal).addPath(record.path);
  }
  backgroundPaths={normal,major};
  backgroundVersion++;
}
function paintBackgroundRoads(isGraph){
    const f=scale*zoom,dpr=devicePixelRatio||1,key=[backgroundVersion,isGraph,dpr].join('|');
    // A still-valid full-quality raster is cheaper than making a preview (e.g. marker dragging).
    const preview=!isGraph&&roadMovement&&!(backgroundRaster?.key===key&&!backgroundRaster.preview);
    if(backgroundRaster?.key!==key||backgroundRaster.preview!==preview){
      const began=performance.now();
    const surface=backgroundRaster?.surface||document.createElement('canvas');surface.width=Math.ceil((width+96)*dpr);surface.height=Math.ceil((height+96)*dpr);
    const brush=surface.getContext('2d');brush.setTransform(dpr,0,0,dpr,0,0);brush.translate(48+width/2+visiblePan[0],48+height/2+visiblePan[1]);brush.scale(f,f);brush.lineCap='round';
      const stroke=(path,color,pixels)=>{brush.strokeStyle=color;brush.lineWidth=pixels/f;brush.stroke(path);perfStats.backgroundStrokeCalls++;};
      if(isGraph){stroke(backgroundPaths.normal,'#385365',1);stroke(backgroundPaths.major,'#385365',1);}
      else if(preview){stroke(backgroundPaths.normal,'#fefefe',1);stroke(backgroundPaths.major,'#fefefe',2);}
      else{stroke(backgroundPaths.normal,'#b7c6d1',3.5);stroke(backgroundPaths.major,'#b7c6d1',6);stroke(backgroundPaths.normal,'#fefefe',1.7);stroke(backgroundPaths.major,'#fefefe',3.7);}
      backgroundRaster={surface,key,preview};perfStats.backgroundRoadStrokes=visibleRoads.length*(isGraph||preview?1:2);perfStats.roadStrokes+=perfStats.backgroundRoadStrokes;
      perfStats.roadBuildMs=performance.now()-began;
    }
    perfStats.roadQuality=backgroundRaster.preview?'movement':'full';
  ctx.drawImage(backgroundRaster.surface,pan[0]-visiblePan[0]-48,pan[1]-visiblePan[1]-48,width+96,height+96);
}
function renderMap() {
  if(!graph)return;
    const began=performance.now();perfStats.frames++;perfStats.roadStrokes=0;perfStats.backgroundRoadStrokes=0;perfStats.backgroundStrokeCalls=0;perfStats.roadBuildMs=0;currentBounds=viewportBounds();
  const viewKey=[width,height,scale,zoom].join('|');
  if(viewKey!==visibleKey||Math.abs(pan[0]-visiblePan[0])>32||Math.abs(pan[1]-visiblePan[1])>32){visibleRoads=roadIndex.query(currentBounds);visibleKey=viewKey;visiblePan=[...pan];cacheBackgroundPaths();}
  perfStats.visibleRoads=visibleRoads.length;
  const isGraph = state.view === 'graph';
  ctx.fillStyle = isGraph ? '#102b40' : '#e7edf1'; ctx.fillRect(0, 0, width, height); ctx.lineCap = 'round';
  paintBackgroundRoads(isGraph);
  const r=state.results[state.algorithm],showSearch=$('visualize').checked&&state.comparison!=='routes';
  if(r!==searchResult||state.playIndex<searchIndex){searchResult=r;searchIndex=0;searchExplored.clear();searchFrontier.clear();}
  if(showSearch&&r)for(;searchIndex<Math.min(state.playIndex,r.events.length);searchIndex++){
    const event=r.events[searchIndex];if(event.type==='expand'){searchExplored.add(event.node);searchFrontier.delete(event.node);}else if(!searchExplored.has(event.node))searchFrontier.add(event.node);
  }
  const frontier=searchFrontier,explored=searchExplored;
  if (showSearch) for (const id of explored) { const p = screen(graph.nodes.get(id));if(p[0]<-5||p[0]>width+5||p[1]<-5||p[1]>height+5)continue; ctx.beginPath(); ctx.arc(...p, isGraph ? 2.3 : 1.6, 0, Math.PI * 2); ctx.fillStyle = isGraph ? '#6d9bb7' : '#5388b394'; ctx.fill(); }
  if (isGraph) {
    const nodeIds=new Set(),arrowEdges=[];
    for(const record of visibleRoads)for(const e of record.directed){nodeIds.add(e.from);nodeIds.add(e.to);arrowEdges.push(e);}
    for(const endpoint of [state.start,state.target])if(endpoint?.nodeId)nodeIds.add(endpoint.nodeId);
    const cells=new Set(),pixelScale=scale*zoom,spacing=pixelScale<.06?16:pixelScale<.15?8:0;
    for(const id of nodeIds){const n=graph.nodes.get(id);if(!n)continue;const p=screen(n);if(p[0]<0||p[0]>width||p[1]<0||p[1]>height)continue;
      const key=Math.floor(p[0]/spacing)+','+Math.floor(p[1]/spacing);if(spacing&&cells.has(key))continue;if(spacing)cells.add(key);
      ctx.beginPath();ctx.arc(...p,zoom>2?2:1,0,2*Math.PI);ctx.fillStyle='#a1b8c6';ctx.fill();
    }
    if(pixelScale>.2)for(const e of arrowEdges){
      const a=screen(baseGraph.nodes.get(e.from)),b=screen(baseGraph.nodes.get(e.to)),length=Math.hypot(b[0]-a[0],b[1]-a[1]);if(length<16)continue;
      const x=a[0]+.65*(b[0]-a[0]),y=a[1]+.65*(b[1]-a[1]);if(x<0||x>width||y<0||y>height)continue;
      const angle=Math.atan2(b[1]-a[1],b[0]-a[0]);ctx.beginPath();ctx.moveTo(x-4*Math.cos(angle-.5),y-4*Math.sin(angle-.5));ctx.lineTo(x,y);ctx.lineTo(x-4*Math.cos(angle+.5),y-4*Math.sin(angle+.5));ctx.strokeStyle='#819bad';ctx.lineWidth=1;ctx.stroke();
    }
  } else if($('street-names').checked) {
    const labels = new Set(), occupied = [];
    ctx.font = '12px Segoe UI, Arial'; ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
    const labelLimit=scale*zoom<.06?14:scale*zoom<.15?30:70;
    for (const record of visibleRoads) {
      if(labels.size>=labelLimit)break;const e=record.edge;
      if(scale*zoom<.06&&!['motorway','trunk','primary','secondary'].includes(e.highway))continue;
      if (!e.name || labels.has(e.name) || e.highway === 'service') continue;
      const [x,y]=screen(record.midpoint);
      if (x < 70 || x > width - 70 || y < 65 || y > height - 65 || occupied.some(p => Math.abs(p[0] - x) < 110 && Math.abs(p[1] - y) < 26)) continue;
      ctx.strokeStyle = '#edf2f5'; ctx.lineWidth = 4; ctx.strokeText(e.name, x, y); ctx.fillStyle = '#547084'; ctx.fillText(e.name, x, y);
      labels.add(e.name); occupied.push([x, y]);
    }
  }
  for(const d of state.disruptions)if(!d.suspended)for(const edge of sectionGeometry.get(d.section.id))line(edge,d.kind==='closure'?'#d34443':'#de981c',10);
  const highlight=sectionIndex.byEdge.get(state.preview||state.selected);
  if(highlight)for(const edge of sectionGeometry.get(highlight.id))line(edge,'#aa51cf80',14);
  if(state.comparison==='routes'){
    for(const [objective,color,lineWidth] of [['fastest','#007e70',8],['shortest','#b249bb',4]]){
      const compared=state.optimalRoutes[objective];if(!compared?.found)continue;
      ctx.setLineDash(objective==='shortest'?[10,7]:[]);
      for(const id of compared.edgeIds)line(graph.edges.get(id),color,lineWidth);
    }
    ctx.setLineDash([]);
  } else if (r && state.playIndex >= r.events.length) {
    for (const id of r.edgeIds) line(graph.edges.get(id), '#fff', 7);
    for (const id of r.edgeIds) line(graph.edges.get(id), isGraph ? '#4de5bf' : '#007e70', 4);
  }
  if (showSearch) for (const id of frontier) { const p = screen(graph.nodes.get(id));if(p[0]<-5||p[0]>width+5||p[1]<-5||p[1]>height+5)continue; ctx.beginPath(); ctx.arc(...p, 3, 0, 2 * Math.PI); ctx.fillStyle = '#e9ab31'; ctx.fill(); }
  for (const d of state.disruptions) {
    const [x,y]=screen(d.suspended&&d.dragPosition?d.dragPosition:d.section.anchor);ctx.fillStyle='white';ctx.beginPath();ctx.arc(x,y,17,0,Math.PI*2);ctx.fill();ctx.font='18px Segoe UI Emoji';ctx.textAlign='center';ctx.textBaseline='middle';ctx.fillText(d.kind==='closure'?'⛔':'🚧',x,y);
    ctx.font='bold 11px Segoe UI';ctx.fillStyle=isGraph?'white':'#102b40';ctx.fillText(traySlots[d.slot].group==='closure'?d.slot.slice(-1):(traySlots[d.slot].group==='custom'?'C':d.percent+'%')+'·'+d.slot.slice(-1),x+17,y-14);
  }
  if(isGraph && $('road-details').checked && state.selected){
    const e=baseGraph.edges.get(state.selected),[x,y]=screen(roadIndex.byEdge.get(e.id).midpoint);
    ctx.fillStyle='#fff';ctx.font='14px Segoe UI';ctx.fillText(state.objective==='shortest'?formatM(e.distance_m):e.base_time_s.toFixed(1)+' s',x,y-15);
  }
  for (const [name, endpoint, color] of [['A', state.start, '#007e70'], ['B', state.target, '#b94a2c']]) {
    if (!endpoint) continue; const [x, y] = screen(endpoint);
    ctx.beginPath(); ctx.arc(x, y, 15, 0, Math.PI * 2); ctx.fillStyle = color; ctx.fill(); ctx.strokeStyle = '#fff'; ctx.lineWidth = 3; ctx.stroke();
    ctx.fillStyle = 'white'; ctx.font = 'bold 14px Segoe UI'; ctx.textAlign = 'center'; ctx.textBaseline = 'middle'; ctx.fillText(name, x, y + .5);
  }
  if(state.car){const [x,y]=screen(state.car);ctx.fillStyle='#ffcc55';ctx.strokeStyle='#102b40';ctx.lineWidth=2;ctx.beginPath();ctx.roundRect(x-10,y-6,20,12,4);ctx.fill();ctx.stroke();ctx.fillStyle='#102b40';ctx.fillRect(x-4,y-4,7,8);}
  $('step').textContent=(showSearch?explored.size:r?.expandedCount??0).toLocaleString()+' expanded';
  perfStats.lastFrameMs=performance.now()-began;
}
function resize() { const rect = canvas.getBoundingClientRect(); width = rect.width; height = rect.height; const dpr = devicePixelRatio || 1; canvas.width = width * dpr; canvas.height = height * dpr; ctx.setTransform(dpr, 0, 0, dpr, 0, 0);scale = Math.min(width / 3100, height / 4000);if(state.start&&state.target)fitRoute();else draw(); }
function selectRoad(id) {
  state.selected = id; const e = baseGraph?.edges.get(id);
  $('route-segment').value = [...$('route-segment').options].some(o => o.value === id) ? id : '';
  $('selected-road').textContent = e ? sectionIndex.byEdge.get(e.id).name + ' · ' + formatM(sectionIndex.byEdge.get(e.id).lengthM) + ' section' : 'No road selected';
  $('add-closure').disabled = $('add-slowdown').disabled = !e; roadMath(); draw();
}
function removeDisruption(slot) {
  state.disruptions=state.disruptions.filter(d=>d.slot!==slot);state.editing=null;state.slot=null;state.preview=null;
  $('update-slowdown').hidden=true;renderDisruptions();calculate();
}
function editDisruption(d) {
  state.editing=d.slot;state.slot=null;selectRoad(d.edges[0]);$('road-details').checked=true;roadMath();
  if(d.kind==='slowdown') {
    $('slowdown').value=traySlots[d.slot].group;
    $('custom-slowdown').value=d.percent;$('custom-slowdown').hidden=$('slowdown').value!=='custom';
  }
  $('update-slowdown').hidden=traySlots[d.slot].group!=='custom';
  status('Editing '+slotLabel(d.slot)+' on '+d.name+'. '+(traySlots[d.slot].group==='custom'?'Set 1–90% and Update, or move the marker.':'This marker has a fixed meaning. Choose Move or drag its map marker.'));
}
function armSlot(slot) {
  state.slot=slot;state.editing=null;state.placing=null;
  const spec=traySlots[slot];if(spec.kind==='slowdown'){$('slowdown').value=spec.group;$('custom-slowdown').hidden=spec.group!=='custom';}
  $('update-slowdown').hidden=true;
  $('set-a').classList.remove('active');$('set-b').classList.remove('active');
  renderDisruptions();status('Choose a road on the map, or a route section and Apply. Escape cancels.');
}
function renderDisruptions() {
  $('disruptions').replaceChildren();
  for(const button of document.querySelectorAll('[data-slot]')) {
    const slot=button.dataset.slot,d=state.disruptions.find(d=>d.slot===slot),kind=slot.startsWith('closure')?'closure':'slowdown';
    button.classList.toggle('active',state.slot===slot);button.classList.toggle('placed',Boolean(d));
    button.textContent=(kind==='closure'?'⛔':'🚧')+' '+slot.slice(-1);
    button.setAttribute('aria-label',slotLabel(slot)+' · '+(d?'Placed':'Unused'));
    button.title=slotLabel(slot)+' · '+(d?d.name+' · '+(kind==='slowdown'?d.percent+'% · ':'')+formatM(d.section.lengthM):'Unused — drag onto a road, or click then choose a road');
  }
  state.disruptions.forEach(d=>{
    const li=document.createElement('li'),body=document.createElement('div'),edit=document.createElement('button'),detail=document.createElement('small'),actions=document.createElement('div');
    li.draggable=true;li.dataset.slot=d.slot;li.dataset.section=d.key;li.ondragstart=event=>{event.dataTransfer.setData('text/plain',JSON.stringify({slot:d.slot,remove:d.key}));beginMove(d.slot);};
    li.ondragend=cancelMove;
    edit.textContent=(d.kind==='closure'?'⛔ ':'🚧 ')+slotLabel(d.slot)+' · '+d.name;edit.className='text-button';edit.onclick=()=>editDisruption(d);
    detail.textContent=formatM(d.section.lengthM)+' · '+(d.kind==='closure'?'Road Closed':'−'+d.percent+'% speed');
    for(const [label,action] of [['Move',()=>armSlot(d.slot)],['Remove',()=>removeDisruption(d.slot)]]){const button=document.createElement('button');button.textContent=label;button.onclick=action;actions.append(button);}
    body.append(edit,detail,actions);li.append(body);$('disruptions').append(li);
  });
  $('clear').disabled=state.disruptions.length===0;
}
function addDisruption(kind,slot=state.slot) {
  if(!state.selected)return false;
  const section=sectionIndex.byEdge.get(state.selected),existing=state.disruptions.find(d=>d.slot===slot);
  if(state.disruptions.some(d=>d.key===section.id && d!==existing)){cancelMove();status('This section already has a disruption. Move or remove it first.');return false;}
  const explicitSlot=!!slot,group=kind==='closure'?'closure':$('slowdown').value;
  slot=slot||Object.keys(traySlots).find(id=>traySlots[id].group===group&&!state.disruptions.some(d=>d.slot===id));
  if(!slot){status('All three markers of this type are placed. Move or remove one, or choose another slowdown type.');return false;}
  const spec=traySlots[slot];if(!spec)return false;
  kind=spec.kind;
  const percent=kind==='closure'?0:spec.percent??existing?.percent??(explicitSlot?40:Number($('custom-slowdown').value));
  if(kind==='slowdown'&&(!Number.isFinite(percent)||percent<1||percent>90)){status('Choose a reduction from 1–90%. Use a closure for 100%.');return false;}
  state.disruptions=state.disruptions.filter(d=>d.slot!==slot);
  state.disruptions.push({key:section.id,slot,kind,percent,edges:section.edgeIds,name:section.name,section});
  state.slot=null;state.editing=null;state.preview=null;$('update-slowdown').hidden=true;
  selectRoad(null);renderDisruptions();calculate();
  if(spec.group==='custom'&&!existing)editDisruption(state.disruptions.find(d=>d.slot===slot));
  return true;
}
function beginMove(slot) {
  const d=state.disruptions.find(d=>d.slot===slot);
  if(d&&!d.suspended){d.suspended=true;stop();stopDrive();status('Moving disruption — route updates on drop.');draw();}
}
function cancelMove() {
  for(const d of state.disruptions){d.suspended=false;delete d.dragPosition;}
  state.preview=null;draw();
}
function moveDisruptionPreview(x,y){
  state.preview=closestRoad(x,y);
  // Visual position only: leave the original section/edges intact until drop.
  for(const d of state.disruptions)if(d.suspended)d.dragPosition=geo(x,y);
  draw();
}
function overElement(id,event){const r=$(id).getBoundingClientRect();return event.clientX>=r.left&&event.clientX<=r.right&&event.clientY>=r.top&&event.clientY<=r.bottom;}
function finishMove(slot,event) {
  if(overElement('disruption-tray',event)||overElement('trash',event)){removeDisruption(slot);return;}
  if(overElement('map',event)){
    const rect=canvas.getBoundingClientRect(),id=closestRoad(event.clientX-rect.left,event.clientY-rect.top);
    if(id){selectRoad(id);if(addDisruption(slot.startsWith('closure')?'closure':'slowdown',slot))return;}
  }
  cancelMove();
}
function placing(which) { state.slot=null;state.placing = which; $('set-a').classList.toggle('active', which === 'start'); $('set-b').classList.toggle('active', which === 'target'); if (which) status('Place ' + (which === 'start' ? 'A' : 'B') + ': click the map or press arrow keys. Enter finishes.'); }
function place(which, point) { state[which] = roadIndex.snap(point); calculate(); }
function closestRoad(x,y){const f=scale*zoom;return roadIndex.hit((x-width/2-pan[0])/f,(y-height/2-pan[1])/f,15/f);}
function setComparison(mode,requested=false){
  state.comparison=mode;algorithmComparisonRequested=mode==='algorithms'&&requested;
  $('algorithm-panel').hidden=mode!=='algorithms';$('routes-panel').hidden=mode!=='routes';
  for(const m of ['algorithms','routes'])$('compare-'+m).setAttribute('aria-pressed',String(mode===m));
  document.querySelector('.map-legend').innerHTML=mode==='routes'?'<i class="route-line"></i>Fastest <i style="background:#b249bb"></i>Shortest (dashed)':'<i class="route-line"></i>Route <i class="search-line"></i>Explored <i class="slowdown-line"></i>Slowed <i class="closure-line"></i>Closed';
  $('route-overlay-legend').hidden=mode!=='routes';
}
function wire() {
  $('full-model').ontoggle=updateFullModel;
  for(const id of ['street-names','visualize'])$(id).onchange=draw;
  $('road-details').onchange=()=>{roadMath();draw();};
  $('fit-route').onclick=fitRoute;$('whole-area').onclick=wholeArea;
  for(const mode of ['algorithms','routes'])$('compare-'+mode).onclick=()=>{setComparison(mode,true);calculate(true);};
  new IntersectionObserver(entries=>{
    const visible=entries[0].isIntersecting;if(visible===algorithmPanelVisible)return;algorithmPanelVisible=visible;
    if(visible&&state.comparison==='algorithms'&&state.start&&Object.keys(state.results).length<3&&!drag&&!state.disruptions.some(d=>d.suspended))calculate(true);
  }).observe($('algorithm-panel'));
  $('reset').onclick=()=>{
    state.disruptions=[];state.delays=null;state.algorithm='dijkstra';state.objective='fastest';state.placing=null;
    state.slot=null;state.editing=null;state.preview=null;$('update-slowdown').hidden=true;
    $('algorithm').value='dijkstra';$('objective').value='fastest';$('journey').value='0';$('slowdown').value='50';$('custom-slowdown').hidden=true;
    $('delay-enabled').checked=false;$('model').value='basic';for(const id of ['delay','delay-stop','delay-signal']){$(id).value=0;$(id).disabled=true;}
    $('street-names').checked=true;$('visualize').checked=false;$('road-details').checked=false;placing(null);$('gps').click();setComparison('algorithms');renderDisruptions();setSample(0);
  };
  $('route-segment').onchange = () => selectRoad($('route-segment').value || null);
  $('journey').onchange = () => setSample(Number($('journey').value));
  $('objective').onchange = () => { state.objective = $('objective').value; calculate(); };
  $('algorithm').onchange = () => { state.algorithm = $('algorithm').value; calculate(); };
  $('swap').onclick = () => { [state.start, state.target] = [state.target, state.start]; calculate(); };
  $('set-a').onclick = () => placing(state.placing === 'start' ? null : 'start');
  $('set-b').onclick = () => placing(state.placing === 'target' ? null : 'target');
  for (const view of ['gps', 'graph']) $(view).onclick = () => { state.view = view; for (const v of ['gps', 'graph']) $(v).setAttribute('aria-pressed', String(v === view)); $('map-mode').textContent = view === 'gps' ? 'GEOGRAPHIC STREET NETWORK' : 'DIRECTED GRAPH · ZOOM FOR ARROWS'; draw(); };
  $('add-closure').onclick = () => addDisruption('closure'); $('add-slowdown').onclick = () => addDisruption('slowdown');
  $('slowdown').onchange = () => { $('custom-slowdown').hidden = $('slowdown').value !== 'custom'; };
  $('clear').onclick = () => { state.disruptions = [];state.editing=null;state.slot=null;$('update-slowdown').hidden=true;renderDisruptions(); calculate(); };
  $('update-slowdown').onclick=()=>{
    const d=state.disruptions.find(d=>d.slot===state.editing),p=Number($('slowdown').value==='custom'?$('custom-slowdown').value:$('slowdown').value);
    if(!d||traySlots[d.slot].group!=='custom')return;
    if(!Number.isFinite(p)||p<1||p>90){status('Choose a reduction from 1–90%.');return;}
    d.percent=p;renderDisruptions();calculate();
  };
  function delayChanged() {
    const values={ordinary:Number($('delay').value),stop:Number($('delay-stop').value),signal:Number($('delay-signal').value)};
    if (Object.values(values).some(v=>!Number.isFinite(v)||v<0||v>120)) { status('Choose delays between 0 and 120 seconds.'); return; }
    for(const id of ['delay','delay-stop','delay-signal'])$(id).disabled=!$('delay-enabled').checked;
    state.delays=$('delay-enabled').checked?values:null;calculate();
  }
  $('model').onchange=()=>{$('delay-enabled').checked=$('model').value==='delays';delayChanged();};
  for(const id of ['delay-enabled','delay','delay-stop','delay-signal'])$(id).onchange=delayChanged;
  function zoomBy(factor) { roadMotion();const old=zoom;zoom = Math.max(.025, Math.min(30, zoom * factor));pan=pan.map(p=>p*zoom/old); draw(); }
  $('zoom-in').onclick = () => zoomBy(1.4); $('zoom-out').onclick = () => zoomBy(1 / 1.4);
  $('fit').onclick = fitRoute;
  canvas.addEventListener('wheel', e => { e.preventDefault(); zoomBy(e.deltaY < 0 ? 1.12 : 1 / 1.12); }, { passive: false });
  const coords = e => { const r = canvas.getBoundingClientRect(); return [e.clientX - r.left, e.clientY - r.top]; };
  for(const button of document.querySelectorAll('[data-slot]')){
    button.ondragstart=e=>{e.dataTransfer.setData('text/plain',JSON.stringify({slot:button.dataset.slot}));beginMove(button.dataset.slot);};
    button.ondragend=cancelMove;
    button.onclick=()=>{const d=state.disruptions.find(d=>d.slot===button.dataset.slot);if(d)editDisruption(d);else armSlot(button.dataset.slot);};
    let trayDrag=null;
    button.onpointerdown=e=>{if(e.button!==0)return;e.preventDefault();button.setPointerCapture(e.pointerId);trayDrag={x:e.clientX,y:e.clientY,moved:false};};
    button.onpointermove=e=>{if(!trayDrag)return;queuePointer(()=>{if(!trayDrag)return;if(Math.hypot(e.clientX-trayDrag.x,e.clientY-trayDrag.y)>5){if(!trayDrag.moved)beginMove(button.dataset.slot);trayDrag.moved=true;
      const rect=canvas.getBoundingClientRect();moveDisruptionPreview(e.clientX-rect.left,e.clientY-rect.top);}});};
    button.onpointerup=e=>{flushPointer();if(!trayDrag)return;if(trayDrag.moved)finishMove(button.dataset.slot,e);else button.click();trayDrag=null;};
    button.onpointercancel=()=>{pendingPointer=null;trayDrag=null;cancelMove();};
  }
  canvas.ondragover=e=>{e.preventDefault();queuePointer(()=>moveDisruptionPreview(...coords(e)));};
  canvas.ondragleave=()=>{pendingPointer=null;state.preview=null;draw();};
  canvas.ondrop=e=>{e.preventDefault();flushPointer();try{
    const value=JSON.parse(e.dataTransfer.getData('text/plain'));
    const slot=value.slot,kind=slot?(slot.startsWith('closure')?'closure':'slowdown'):value.kind;
    if(!['closure','slowdown'].includes(kind))return;
    const id=closestRoad(...coords(e));if(!id){cancelMove();status('Drop closer to a road.');return;}
    selectRoad(id);addDisruption(kind,slot);
  }catch{cancelMove();status('Choose a slowdown or closure marker.');}};
  for(const id of ['trash','disruption-tray']){
    $(id).ondragover=e=>{e.preventDefault();$(id).classList.add('over');};
    $(id).ondragleave=()=>$(id).classList.remove('over');
    $(id).ondrop=e=>{e.preventDefault();$(id).classList.remove('over');try{const data=JSON.parse(e.dataTransfer.getData('text/plain')),d=state.disruptions.find(d=>d.slot===data.slot||d.key===data.remove);if(d)removeDisruption(d.slot);}catch{cancelMove();}};
  }
  canvas.onpointerdown = e => {
    const [x, y] = coords(e); canvas.setPointerCapture(e.pointerId); let endpoint = null, disruption=null;
    for(const d of state.disruptions){const p=screen(d.section.anchor);if(Math.hypot(x-p[0],y-p[1])<22)disruption=d.slot;}
    for (const key of ['start', 'target']) { const p = screen(state[key]); if (Math.hypot(x - p[0], y - p[1]) < 22) endpoint = key; }
    if(endpoint){disruption=null;stop();stopDrive();}
    drag = { x, y, lastX: x, lastY: y, endpoint, disruption, moved: false, original:endpoint?state[endpoint]:null };
  };
  const movePointer = e => {
    if (!drag) return; const [x, y] = coords(e);
    if (Math.hypot(x - drag.x, y - drag.y) > 4) drag.moved = true;
    if (drag.endpoint) { state[drag.endpoint] = roadIndex.snap(geo(x,y)); draw(); }
    else if(drag.disruption&&drag.moved){beginMove(drag.disruption);moveDisruptionPreview(x,y);$('trash').classList.toggle('over',overElement('trash',e));}
    else if (drag.moved) { roadMotion();pan[0] += x - drag.lastX; pan[1] += y - drag.lastY; draw(); }
    drag.lastX = x; drag.lastY = y;
  };
  canvas.onpointermove=e=>{if(drag)queuePointer(()=>movePointer(e));};
  canvas.onpointerup = e => {
    flushPointer();
    endRoadMotion();
    if (!drag) return; const [x, y] = coords(e);
    if(drag.disruption){if(drag.moved)finishMove(drag.disruption,e);else{const d=state.disruptions.find(d=>d.slot===drag.disruption);if(d)editDisruption(d);}$('trash').classList.remove('over');}
    else if (drag.endpoint) {if(drag.moved){state[drag.endpoint]=roadIndex.snap(geo(x,y));calculate();}}
    else if (!drag.moved && state.slot) {const id=closestRoad(x,y);if(id){selectRoad(id);addDisruption(state.slot.startsWith('closure')?'closure':'slowdown');}}
    else if (!drag.moved && state.placing) { place(state.placing, geo(x, y)); placing(null); }
    else if (!drag.moved) selectRoad(closestRoad(x, y)); drag = null;
  };
  canvas.onpointercancel = () => {endRoadMotion();pendingPointer=null;if(drag?.endpoint)state[drag.endpoint]=drag.original;drag=null;cancelMove();};
  document.addEventListener('keydown', e => {
    if(e.key==='Escape'){if(drag?.disruption){pendingPointer=null;drag=null;$('trash').classList.remove('over');}state.slot=null;state.editing=null;$('update-slowdown').hidden=true;renderDisruptions();cancelMove();}
    if (!state.placing || ['INPUT', 'SELECT'].includes(document.activeElement.tagName)) return;
    if (e.key === 'Escape' || e.key === 'Enter') { placing(null); return; }
    const delta = { ArrowLeft: [-50, 0], ArrowRight: [50, 0], ArrowUp: [0, -50], ArrowDown: [0, 50] }[e.key];
    if (delta) { e.preventDefault(); const p = screen(state[state.placing]); place(state.placing, geo(p[0] + delta[0], p[1] + delta[1])); }
  });
  $('progress').oninput = () => { stop(); state.playIndex = Number($('progress').value); draw(); };
  $('play').onclick = () => {
    $('visualize').checked=true;stopDrive();
    if (state.playing) { stop(); return; }
    const r = state.results[state.algorithm]; if (state.playIndex >= r.events.length) state.playIndex = 0;
    state.playing = true; $('play').textContent = 'Ⅱ Pause'; let last = 0;
    const animate = now => { if (!state.playing) return; if (now - last > 30) { state.playIndex = Math.min(r.events.length, state.playIndex + Math.max(1, Math.ceil(r.events.length / 180))); $('progress').value = state.playIndex; draw(); last = now; } if (state.playIndex < r.events.length) frame = requestAnimationFrame(animate); else stop(); };
    frame = requestAnimationFrame(animate);
  };
  $('drive').onclick=()=>{
    const r=state.results[state.algorithm];if(!r.found||r.timeS<=0)return;
    const duration=Math.max(10,Math.min(20,r.timeS/30));
    stop();state.playIndex=r.events.length;state.driving=true;$('drive').disabled=true;$('drive').textContent='Driving · '+duration.toFixed(0)+' s';
    const started=performance.now();
    const animate=now=>{
      const fraction=Math.min(1,(now-started)/(duration*1000)),modelTime=fraction*r.timeS;
      let cumulative=0;
      for(const leg of r.legs){
        const e=graph.edges.get(leg.edgeId),end=cumulative+leg.travelS+leg.delayS;
        if(modelTime<=end){state.car=cachedPointAlong(cachedGeometry(graph,e),Math.min(1,(modelTime-cumulative)/leg.travelS));break;}
        cumulative=end;
      }
      draw();
      if(fraction<1)driveFrame=requestAnimationFrame(animate);else{stopDrive();$('drive').disabled=false;draw();}
    };
    driveFrame=requestAnimationFrame(animate);
  };
}
async function init() {
  try {
    
    raw = JSON.parse((await Promise.all(["graph-1-b87d27e1e716.txt","graph-2-b87d27e1e716.txt","graph-3-b87d27e1e716.txt","graph-4-b87d27e1e716.txt","graph-5-b87d27e1e716.txt"].map(async name => {const response = await fetch(new URL(name, import.meta.url)); if (!response.ok) throw new Error('Road data response ' + response.status); return response.text();}))).join('')); baseGraph = prepareGraph(raw); graph=baseGraph;
    roadIndex=new RoadSpatialIndex(baseGraph);routeSession=new RouteSession(baseGraph);
    sectionIndex=buildSections(baseGraph);for(const section of sectionIndex.sections.values())sectionGeometry.set(section.id,section.representativeIds.map(id=>baseGraph.edges.get(id)));const connected=connectivity(baseGraph);baseGraph.snapNodes=connected.main;
    samples=journeys.map(e=>[e.from,e.to]);$('journey').replaceChildren(...journeys.map((e,i)=>new Option(e.label,String(i))));
    $('connectivity-note').textContent='Endpoint snapping uses the largest mutually reachable road component ('+connected.main.size.toLocaleString()+' vertices). Other roads remain visible; turn restrictions and closures can still make a route unavailable.';
    const m=raw.metadata;
    $('speed-assumptions').textContent='Missing-speed model inputs (km/h): '+Object.entries(m.default_speed_kmh).map(([k,v])=>k.replaceAll('_',' ')+' '+v).join('; ')+'. These conservative class-based values are modelling assumptions, not verified speed limits. Basic defaults to zero intersection delay; the IA sensitivity scenario uses 3 s ordinary / 8 s stop / 20 s signal, all adjustable and unmeasured.';
    $('model-note').textContent = raw.nodes.length.toLocaleString() + ' vertices · ' + raw.edges.length.toLocaleString() + ' directed edges · '+m.restriction_count+' simple turn restrictions imported. '+(m.restriction_status?.startsWith('unavailable')?'Restriction data unavailable; this does not mean no restrictions exist. ':'')+m.speed_source_edge_counts.osm_maxspeed+' directed edges use OSM speeds; '+m.speed_source_edge_counts.road_type_assumption+' use assumptions. Snapshot '+m.osm_base_timestamp.slice(0,10)+'. Curved geometry is retained.';
    wire();renderDisruptions(); resize(); new ResizeObserver(resize).observe(canvas); setSample(0);
  } catch (error) { status('Unable to load or initialize the simulator: ' + error.message + '. Reload to retry.'); console.error(error); return; }
  const registry = document.modelContext;
  if (registry?.registerTool) {
    const lifecycle = new AbortController(); window.addEventListener('pagehide', () => lifecycle.abort(), { once: true });
    try {
      await registry.registerTool({ name: 'read_route_comparison', description: 'Read the current Halifax route comparisons and model settings.', inputSchema: { type: 'object', properties: {}, additionalProperties: false }, annotations: { readOnlyHint: true },
        execute(input) { if (!input || typeof input !== 'object' || Object.keys(input).length) throw new Error('Expected an empty object'); return { objective: state.objective, algorithm: state.algorithm, results: Object.fromEntries(Object.entries(state.results).map(([k, r]) => [k, { found: r.found, distanceM: r.distanceM, timeS: r.timeS, expanded: r.expandedCount }])) }; } }, { signal: lifecycle.signal });
    } catch (error) { console.warn('Optional route tool unavailable', error); }
  }
}
// Read-only diagnostics for automated regression/performance checks; no UI or storage.
export function performanceSnapshot(){
  const rect=canvas.getBoundingClientRect(),position=p=>{const [x,y]=screen(p);return {x:x+rect.left,y:y+rect.top};};
  return {...perfStats,routing:{...routeSession?.stats},totalPhysicalRoads:roadIndex?.records.length,computedAlgorithms:Object.keys(state.results),
    markers:{a:state.start?position(state.start):null,b:state.target?position(state.target):null,disruptions:state.disruptions.map(d=>({slot:d.slot,percent:d.percent,suspended:!!d.suspended,section:d.key,...position(d.suspended&&d.dragPosition?d.dragPosition:d.section.anchor)}))},
    selected:state.results[state.algorithm]?{cost:state.results[state.algorithm].cost,distanceM:state.results[state.algorithm].distanceM,timeS:state.results[state.algorithm].timeS,edgeIds:[...state.results[state.algorithm].edgeIds]}:null};
}
init();
