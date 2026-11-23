(() => {
  const svg = document.getElementById('artboard');
  const root = document.getElementById('objectsRoot');
  const selectionRoot = document.getElementById('selectionRoot');
  const layersList = document.getElementById('layersList');
  const toolNames = {select:'Mover camada',pencil:'Lápis',brush:'Pincel',eraser:'Borracha',eyedropper:'Conta-gotas',bucket:'Balde de tinta',text:'Texto',line:'Linha',rect:'Retângulo',ellipse:'Elipse',triangle:'Triângulo'};
  let layers = [{id:'layer-1',name:'Camada 1',visible:true,locked:false}];
  let objects = [];
  let activeLayer = 'layer-1', selectedId = null, tool = 'select';
  let drawing = false, start = null, draft = null, zoom = 1, eraserPath = '', eraserChanged = false;
  let transformDrag = null, transformMode = false;
  let color = '#8b5cf6', stroke = '#252538', strokeWidth = 4, fillEnabled = true;
  let undoStack = [], redoStack = [], dragOffset = null;
  let alignmentGuides = { vertical: false, horizontal: false };
  let activeTextEditor = null;
  let lastShapeTool = 'line';

  const $ = id => document.getElementById(id);
  const uid = () => 'obj-' + Math.random().toString(36).slice(2,10);
  const snapshot = () => JSON.stringify({layers,objects,activeLayer,selectedId});
  function saveHistory(){ undoStack.push(snapshot()); if(undoStack.length>80)undoStack.shift(); redoStack=[]; updateHistoryButtons(); }
  function restore(s){const d=JSON.parse(s);layers=d.layers;objects=d.objects;activeLayer=d.activeLayer;selectedId=d.selectedId;render();}
  function updateHistoryButtons(){$('undoBtn').disabled=!undoStack.length;$('redoBtn').disabled=!redoStack.length;}
  function undo(){if(!undoStack.length)return;redoStack.push(snapshot());restore(undoStack.pop());updateHistoryButtons();}
  function redo(){if(!redoStack.length)return;undoStack.push(snapshot());restore(redoStack.pop());updateHistoryButtons();}
  function currentLayer(){return layers.find(l=>l.id===activeLayer);}
  function attrsFor(obj){return {fill:obj.fill??'none',stroke:obj.stroke??'none','stroke-width':obj.strokeWidth??1,'stroke-linecap':'round','stroke-linejoin':'round','data-object-id':obj.id,opacity:obj.opacity??1};}
  function makeElement(obj){
    let el;
    if(obj.type==='path'){el=document.createElementNS('http://www.w3.org/2000/svg','path');el.setAttribute('d',obj.d);}
    else if(obj.type==='line'){el=document.createElementNS('http://www.w3.org/2000/svg','line');['x1','y1','x2','y2'].forEach(k=>el.setAttribute(k,obj[k]));}
    else if(obj.type==='rect'){el=document.createElementNS('http://www.w3.org/2000/svg','rect');['x','y','width','height','rx'].forEach(k=>{if(obj[k]!=null)el.setAttribute(k,obj[k]);});}
    else if(obj.type==='ellipse'){el=document.createElementNS('http://www.w3.org/2000/svg','ellipse');['cx','cy','rx','ry'].forEach(k=>el.setAttribute(k,obj[k]));}
    else if(obj.type==='polygon'){el=document.createElementNS('http://www.w3.org/2000/svg','polygon');el.setAttribute('points',obj.points);}
    else if(obj.type==='image'){el=document.createElementNS('http://www.w3.org/2000/svg','image');el.setAttribute('x',obj.x);el.setAttribute('y',obj.y);el.setAttribute('width',obj.width);el.setAttribute('height',obj.height);el.setAttribute('href',obj.href);el.setAttribute('preserveAspectRatio','none');}
    Object.entries(attrsFor(obj)).forEach(([k,v])=>el.setAttribute(k,v));
    el.style.cursor='pointer';
    if(obj.erasures && obj.erasures.length){
      const wrap=document.createElementNS('http://www.w3.org/2000/svg','g');
      const maskId='erase-mask-'+obj.id;
      const mask=document.createElementNS('http://www.w3.org/2000/svg','mask');
      mask.setAttribute('id',maskId);
      mask.setAttribute('maskUnits','userSpaceOnUse');
      const white=document.createElementNS('http://www.w3.org/2000/svg','rect');
      white.setAttribute('x','0');white.setAttribute('y','0');white.setAttribute('width','1200');white.setAttribute('height','750');white.setAttribute('fill','white');
      mask.appendChild(white);
      obj.erasures.forEach(d=>{
        const cut=document.createElementNS('http://www.w3.org/2000/svg','path');
        cut.setAttribute('d',d);cut.setAttribute('fill','none');cut.setAttribute('stroke','black');
        cut.setAttribute('stroke-width',String(obj.eraseWidth||24));cut.setAttribute('stroke-linecap','round');cut.setAttribute('stroke-linejoin','round');
        mask.appendChild(cut);
      });
      wrap.appendChild(mask);wrap.appendChild(el);wrap.setAttribute('mask',`url(#${maskId})`);
      return wrap;
    }
    return el;
  }
  const identity = () => [1,0,0,1,0,0];
  function layerMatrix(layer){ if(!layer.matrix) layer.matrix=identity(); return layer.matrix; }
  function multiplyMatrix(a,b){return [a[0]*b[0]+a[2]*b[1],a[1]*b[0]+a[3]*b[1],a[0]*b[2]+a[2]*b[3],a[1]*b[2]+a[3]*b[3],a[0]*b[4]+a[2]*b[5]+a[4],a[1]*b[4]+a[3]*b[5]+a[5]];}
  function around(cx,cy,m){return multiplyMatrix([1,0,0,1,cx,cy],multiplyMatrix(m,[1,0,0,1,-cx,-cy]));}
  function transformPoint(x,y,m){return{x:m[0]*x+m[2]*y+m[4],y:m[1]*x+m[3]*y+m[5]};}
  function inversePoint(x,y,m){const det=m[0]*m[3]-m[1]*m[2]||1;const a=m[3]/det,b=-m[1]/det,c=-m[2]/det,d=m[0]/det;const px=x-m[4],py=y-m[5];return{x:a*px+c*py,y:b*px+d*py};}
  function layerBounds(layerId){const arr=objects.filter(o=>o.layerId===layerId).map(bounds).filter(Boolean);if(!arr.length)return null;const x=Math.min(...arr.map(b=>b.x)),y=Math.min(...arr.map(b=>b.y)),r=Math.max(...arr.map(b=>b.x+b.w)),bt=Math.max(...arr.map(b=>b.y+b.h));const m=layerMatrix(layers.find(l=>l.id===layerId));const pts=[[x,y],[r,y],[r,bt],[x,bt]].map(([a,b])=>transformPoint(a,b,m));const xs=pts.map(p=>p.x),ys=pts.map(p=>p.y);return{x:Math.min(...xs),y:Math.min(...ys),w:Math.max(...xs)-Math.min(...xs),h:Math.max(...ys)-Math.min(...ys),cx:(Math.min(...xs)+Math.max(...xs))/2,cy:(Math.min(...ys)+Math.max(...ys))/2};}
  function setLayerTransform(layer,worldTransform){layer.matrix=multiplyMatrix(worldTransform,layerMatrix(layer));}
  function transformHandles(b){
    const ns='http://www.w3.org/2000/svg'; const g=document.createElementNS(ns,'g');g.setAttribute('class','transform-controls');g.setAttribute('pointer-events','all');
    const pad=0;const x=b.x,y=b.y,r=b.x+b.w,bt=b.y+b.h,cx=b.cx,cy=b.cy;
    const outline=document.createElementNS(ns,'rect');outline.setAttribute('x',x);outline.setAttribute('y',y);outline.setAttribute('width',Math.max(1,b.w));outline.setAttribute('height',Math.max(1,b.h));outline.setAttribute('class','transform-outline');outline.setAttribute('pointer-events','none');g.appendChild(outline);
    const pts=[['nw',x,y],['n',cx,y],['ne',r,y],['e',r,cy],['se',r,bt],['s',cx,bt],['sw',x,bt],['w',x,cy]];
    pts.forEach(([key,px,py])=>{const h=document.createElementNS(ns,'rect');h.setAttribute('x',px-5);h.setAttribute('y',py-5);h.setAttribute('width',10);h.setAttribute('height',10);h.setAttribute('rx',1);h.setAttribute('class','transform-handle');h.dataset.transformHandle=key;g.appendChild(h);});
    const rot=document.createElementNS(ns,'circle');rot.setAttribute('cx',cx);rot.setAttribute('cy',y-27);rot.setAttribute('r',6);rot.setAttribute('class','transform-rotate');rot.dataset.transformHandle='rotate';g.appendChild(rot);
    const stem=document.createElementNS(ns,'line');stem.setAttribute('x1',cx);stem.setAttribute('y1',y);stem.setAttribute('x2',cx);stem.setAttribute('y2',y-21);stem.setAttribute('class','transform-stem');stem.setAttribute('pointer-events','none');g.appendChild(stem);return g;
  }
  function render(){
    root.innerHTML='';
    layers.forEach(layer=>{
      const group=document.createElementNS('http://www.w3.org/2000/svg','g');
      group.dataset.layerId=layer.id; group.style.display=layer.visible?'':'none'; const lm=layerMatrix(layer); group.setAttribute('transform',`matrix(${lm.join(' ')})`);
      objects.filter(o=>o.layerId===layer.id).forEach(o=>group.appendChild(makeElement(o)));
      root.appendChild(group);
    });
    renderSelection();renderLayers();renderProperties();updateCounts();
  }
  function renderSelection(){
    selectionRoot.innerHTML='';
    const b=layerBounds(activeLayer);
    if(b){
      if(alignmentGuides.vertical){const line=document.createElementNS('http://www.w3.org/2000/svg','line');line.setAttribute('x1','600');line.setAttribute('x2','600');line.setAttribute('y1','0');line.setAttribute('y2','750');line.setAttribute('class','alignment-guide');selectionRoot.appendChild(line);}
      if(alignmentGuides.horizontal){const line=document.createElementNS('http://www.w3.org/2000/svg','line');line.setAttribute('x1','0');line.setAttribute('x2','1200');line.setAttribute('y1','375');line.setAttribute('y2','375');line.setAttribute('class','alignment-guide');selectionRoot.appendChild(line);}
      if(transformMode) selectionRoot.appendChild(transformHandles(b));
      else {const r=document.createElementNS('http://www.w3.org/2000/svg','rect');r.setAttribute('x',b.x-7);r.setAttribute('y',b.y-7);r.setAttribute('width',Math.max(10,b.w+14));r.setAttribute('height',Math.max(10,b.h+14));r.setAttribute('fill','none');r.setAttribute('stroke','#6d5ce7');r.setAttribute('stroke-dasharray','6 4');r.setAttribute('pointer-events','none');selectionRoot.appendChild(r);}
    }
    if(tool==='eraser' && eraserCursor)selectionRoot.appendChild(eraserCursor);
  }
  function bounds(o){
    if(o.type==='image')return{x:o.x,y:o.y,w:o.width,h:o.height};
    if(o.type==='rect')return{x:o.x,y:o.y,w:o.width,h:o.height};
    if(o.type==='ellipse')return{x:o.cx-o.rx,y:o.cy-o.ry,w:o.rx*2,h:o.ry*2};
    if(o.type==='line')return{x:Math.min(o.x1,o.x2),y:Math.min(o.y1,o.y2),w:Math.abs(o.x2-o.x1),h:Math.abs(o.y2-o.y1)};
    if(o.type==='polygon'){let p=o.points.trim().split(/\s+/).map(v=>v.split(',').map(Number));let xs=p.map(a=>a[0]),ys=p.map(a=>a[1]);return{x:Math.min(...xs),y:Math.min(...ys),w:Math.max(...xs)-Math.min(...xs),h:Math.max(...ys)-Math.min(...ys)};}
    if(o.type==='path'){let nums=(o.d.match(/-?\d+\.?\d*/g)||[]).map(Number),xs=[],ys=[];for(let i=0;i<nums.length;i+=2){xs.push(nums[i]);ys.push(nums[i+1]);}if(xs.length)return{x:Math.min(...xs),y:Math.min(...ys),w:Math.max(...xs)-Math.min(...xs),h:Math.max(...ys)-Math.min(...ys)};}
    return null;
  }
  function renderLayers(){
    layersList.innerHTML='';
    [...layers].reverse().forEach(layer=>{
      const row=document.createElement('div');row.className='layer-row'+(layer.id===activeLayer?' selected':'');
      const eye=document.createElement('button');eye.className='eye';eye.textContent=layer.visible?'◉':'○';eye.title='Alternar visibilidade';eye.setAttribute('aria-label','Alternar visibilidade');
      eye.onclick=e=>{e.stopPropagation();layer.visible=!layer.visible;render();};
      const thumb=document.createElement('div');thumb.className='layer-thumb';thumb.innerHTML='<svg viewBox="0 0 32 24" aria-hidden="true"><rect x="3" y="3" width="26" height="18" rx="2"/><path d="M7 17l6-7 4 4 3-3 5 6"/><circle cx="22" cy="8" r="2"/></svg>';
      const name=document.createElement('span');name.className='layer-name';name.textContent=layer.name;
      const count=document.createElement('span');count.className='count';count.textContent=objects.filter(o=>o.layerId===layer.id).length;
      const lock=document.createElement('button');lock.className='layer-lock'+(layer.locked?' locked':'');lock.innerHTML=layer.locked?'<svg viewBox="0 0 24 24" aria-hidden="true"><rect x="5" y="10" width="14" height="11" rx="2"/><path d="M8 10V7a4 4 0 0 1 8 0v3"/></svg>':'<svg viewBox="0 0 24 24" aria-hidden="true"><rect x="5" y="10" width="14" height="11" rx="2"/><path d="M8 10V7a4 4 0 0 1 7.5-2"/></svg>';lock.title=layer.locked?'Desbloquear camada':'Bloquear camada';lock.setAttribute('aria-label',lock.title);
      lock.onclick=e=>{e.stopPropagation();saveHistory();layer.locked=!layer.locked;render();};
      row.append(eye,thumb,name,count,lock);row.onclick=()=>{activeLayer=layer.id;selectedId=null;render();};layersList.appendChild(row);
    });
  }
  function renderProperties(){
    const box=$('propertyContent'),o=objects.find(x=>x.id===selectedId),layer=currentLayer();
    if(!o){box.className='muted';box.innerHTML=layer?`<strong>${layer.name}</strong><br>Camada ativa · ${objects.filter(x=>x.layerId===activeLayer).length} objeto(s)<br><br>Use a ferramenta Selecionar para arrastar todo o conteúdo desta camada.`:'Selecione uma camada.';return;}
    box.className='';
    const b=bounds(o)||{x:0,y:0,w:0,h:0};
    box.innerHTML=`<div class="property-form">
      <label class="wide">Tipo<input value="${o.type}" disabled></label>
      <label>Posição X<input data-prop="x" type="number" value="${Math.round(b.x)}"></label>
      <label>Posição Y<input data-prop="y" type="number" value="${Math.round(b.y)}"></label>
      <label>Cor<input data-prop="fill" type="color" value="${o.fill&&o.fill!=='none'?o.fill:'#ffffff'}"></label>
      <label>Contorno<input data-prop="stroke" type="color" value="${o.stroke&&o.stroke!=='none'?o.stroke:'#000000'}"></label>
      <label class="wide">Espessura<input data-prop="strokeWidth" type="number" min="1" max="80" value="${o.strokeWidth||1}"></label>
    </div>`;
    box.querySelectorAll('[data-prop]').forEach(input=>input.addEventListener('change',()=>{
      saveHistory();const key=input.dataset.prop;let val=input.type==='number'?Number(input.value):input.value;
      if(key==='x'||key==='y')moveObject(o,key,val);else o[key]=val;render();
    }));
  }
  function moveObject(o,key,val){const b=bounds(o);if(!b)return;const delta=val-b[key];if(o.type==='rect')o[key]+=delta;else if(o.type==='ellipse')o[key==='x'?'cx':'cy']+=delta;else if(o.type==='line'){o[key==='x'?'x1':'y1']+=delta;o[key==='x'?'x2':'y2']+=delta;}else if(o.type==='polygon'){let pts=o.points.trim().split(/\s+/).map(p=>p.split(',').map(Number));o.points=pts.map(p=>(p[0]+(key==='x'?delta:0))+','+(p[1]+(key==='y'?delta:0))).join(' ');}else if(o.type==='path'){let nums=(o.d.match(/-?\d+\.?\d*/g)||[]).map(Number),i=0;o.d=o.d.replace(/-?\d+\.?\d*/g,()=>{let n=nums[i++];return n+((i%2===1&&key==='x')||(i%2===0&&key==='y')?delta:0);});}}
  function updateCounts(){$('objectCount').textContent=objects.length;$('layerCount').textContent=layers.length;}
  function point(e){const p=svg.createSVGPoint();p.x=e.clientX;p.y=e.clientY;return p.matrixTransform(svg.getScreenCTM().inverse());}
  function localPoint(p){const l=currentLayer();return l?inversePoint(p.x,p.y,layerMatrix(l)):p;}
  function style(){return {fill:fillEnabled?color:'none',stroke,strokeWidth};}
  function addObject(o){o.id=uid();o.layerId=activeLayer;objects.push(o);selectedId=null;render();}
  function setTool(t){tool=t;transformMode=false;document.querySelectorAll('.tool').forEach(b=>b.classList.toggle('active',b.dataset.tool===t));$('shapePickerButton').classList.toggle('active',['line','rect','ellipse','triangle'].includes(t));$('toolName').textContent=toolNames[t];$('statusText').textContent='Ferramenta: '+toolNames[t];svg.style.cursor=t==='select'?'default':t==='eyedropper'?'copy':t==='eraser'?'none':'crosshair'; svg.classList.toggle('eraser-mode',t==='eraser');}
  function hitObject(target){const id=target.closest('[data-object-id]')?.getAttribute('data-object-id');return objects.find(o=>o.id===id);}
  svg.addEventListener('pointerdown',e=>{
    if(e.button!==0)return;const p=point(e),target=hitObject(e.target);
    const handle=e.target.closest?.('[data-transform-handle]')?.dataset.transformHandle;
    if(transformMode && handle){const b=layerBounds(activeLayer);if(!b)return;saveHistory();transformDrag={handle,start:p,center:{x:b.cx,y:b.cy},bounds:b,initial:[...layerMatrix(currentLayer())],startAngle:Math.atan2(p.y-b.cy,p.x-b.cx),startDist:Math.hypot(p.x-b.cx,p.y-b.cy)};svg.setPointerCapture(e.pointerId);return;}
    if(tool==='eyedropper'){if(target){const o=hitObject(e.target);color=o.fill&&o.fill!=='none'?o.fill:o.stroke;$('colorInput').value=color;}return;}
    if(tool==='bucket'){if(target&&!currentLayer()?.locked){const o=hitObject(e.target);if(o){saveHistory();o.fill=color;render();$('statusText').textContent='Preenchimento aplicado.';}}return;}
    if(tool==='text'){if(currentLayer()?.locked){$('statusText').textContent='Esta camada está bloqueada.';return;}beginTextEditor(p,e.clientX,e.clientY);return;}
    if(tool==='eraser'){
      const lp=localPoint(p);
      if(currentLayer()?.locked){$('statusText').textContent='Esta camada está bloqueada.';return;}
      drawing=true;start=lp;eraserPath=`M ${lp.x} ${lp.y}`;eraserChanged=false;saveHistory();svg.setPointerCapture(e.pointerId);return;
    }
    if(tool==='select'){
      selectedId=null;
      if(currentLayer()?.locked){$('statusText').textContent='Esta camada está bloqueada.';render();return;}
      if(objects.some(o=>o.layerId===activeLayer)){dragOffset={x:p.x,y:p.y};saveHistory();svg.setPointerCapture(e.pointerId);}
      render();return;
    }
    if(currentLayer()?.locked){$('statusText').textContent='Esta camada está bloqueada.';return;}
    drawing=true;start=localPoint(p);svg.setPointerCapture(e.pointerId);
    if(tool==='pencil'||tool==='brush'){draft={type:'path',d:`M ${start.x} ${start.y}`,...style(),fill:'none',strokeWidth:tool==='brush'?Math.max(strokeWidth,8):strokeWidth};}
    else draft={type:tool,...style()};
  });
  svg.addEventListener('pointermove',e=>{
    const p=point(e);
    if(transformDrag){const d=transformDrag,b=d.bounds,c=d.center;let m=identity();if(d.handle==='rotate'){const angle=Math.atan2(p.y-c.y,p.x-c.x)-d.startAngle;m=[Math.cos(angle),Math.sin(angle),-Math.sin(angle),Math.cos(angle),0,0];}else{let sx=1,sy=1;const dx=p.x-d.start.x,dy=p.y-d.start.y;const h=d.handle;if(h.includes('e'))sx=(b.w+dx)/Math.max(1,b.w);if(h.includes('w'))sx=(b.w-dx)/Math.max(1,b.w);if(h.includes('s'))sy=(b.h+dy)/Math.max(1,b.h);if(h.includes('n'))sy=(b.h-dy)/Math.max(1,b.h);if(h.length===2){const uniform=Math.max(.02,Math.abs(sx)>Math.abs(sy)?sx:sy);sx=Math.sign(sx||1)*uniform;sy=Math.sign(sy||1)*uniform;}sx=Math.max(.02,sx);sy=Math.max(.02,sy);m=[sx,0,0,sy,0,0];}const aroundM=around(c.x,c.y,m);currentLayer().matrix=multiplyMatrix(aroundM,d.initial);render();return;}
    if(tool==='select'&&dragOffset){let dx=p.x-dragOffset.x,dy=p.y-dragOffset.y;if(dx||dy){const b=layerBounds(activeLayer);alignmentGuides={vertical:false,horizontal:false};if(b){const tolerance=8/zoom;const nextCx=b.cx+dx,nextCy=b.cy+dy;if(Math.abs(nextCx-600)<=tolerance){dx+=600-nextCx;alignmentGuides.vertical=true;}if(Math.abs(nextCy-375)<=tolerance){dy+=375-nextCy;alignmentGuides.horizontal=true;}}const l=currentLayer();l.matrix=multiplyMatrix([1,0,0,1,dx,dy],layerMatrix(l));dragOffset={x:p.x,y:p.y};render();}return;}
    if(tool==='eraser'&&drawing){
      const lp=localPoint(p);eraserPath+=` L ${lp.x} ${lp.y}`;
      const radius=Math.max(8,strokeWidth*3);
      objects.filter(o=>o.layerId===activeLayer).forEach(o=>{
        if(!o.erasures)o.erasures=[];
        o.erasures.push(eraserPath);
        o.eraseWidth=radius*2;
      });
      eraserChanged=true;render();
      eraserPath=`M ${lp.x} ${lp.y}`;
      return;
    }
    if(!drawing||!draft)return;
    let lp=localPoint(p);
    if(e.shiftKey && (draft.type==='rect'||draft.type==='ellipse')){const side=Math.max(Math.abs(lp.x-start.x),Math.abs(lp.y-start.y));lp={x:start.x+Math.sign(lp.x-start.x||1)*side,y:start.y+Math.sign(lp.y-start.y||1)*side};}
    if(draft.type==='path'){draft.d+=` L ${lp.x} ${lp.y}`;}
    else if(draft.type==='line'){Object.assign(draft,{x1:start.x,y1:start.y,x2:lp.x,y2:lp.y});}
    else if(draft.type==='rect'){Object.assign(draft,{x:Math.min(start.x,lp.x),y:Math.min(start.y,lp.y),width:Math.abs(lp.x-start.x),height:Math.abs(lp.y-start.y),rx:0});}
    else if(draft.type==='ellipse'){Object.assign(draft,{cx:(start.x+lp.x)/2,cy:(start.y+lp.y)/2,rx:Math.abs(lp.x-start.x)/2,ry:Math.abs(lp.y-start.y)/2});}
    else if(draft.type==='triangle'){draft.type='polygon';draft.points=`${(start.x+lp.x)/2},${start.y} ${lp.x},${lp.y} ${start.x},${lp.y}`;}
    selectionRoot.innerHTML='';root.querySelector('[data-draft="1"]')?.remove();
    const el=makeElement(draft);el.dataset.draft='1';root.querySelector(`[data-layer-id="${activeLayer}"]`)?.appendChild(el);
  });
  function translate(o,dx,dy){
    if(o.type==='rect'){o.x+=dx;o.y+=dy;}else if(o.type==='ellipse'){o.cx+=dx;o.cy+=dy;}else if(o.type==='text'||o.type==='image'){o.x+=dx;o.y+=dy;}else if(o.type==='line'){o.x1+=dx;o.x2+=dx;o.y1+=dy;o.y2+=dy;}else if(o.type==='polygon'){o.points=o.points.trim().split(/\s+/).map(p=>{let a=p.split(',').map(Number);return(a[0]+dx)+','+(a[1]+dy)}).join(' ');}else if(o.type==='path'){o.d=o.d.replace(/(-?\d+\.?\d*)\s+(-?\d+\.?\d*)/g,(_,x,y)=>(Number(x)+dx)+' '+(Number(y)+dy));}}
  function finishDrawing(){
    if(transformDrag){transformDrag=null;render();return;}
    if(tool==='select'){dragOffset=null;alignmentGuides={vertical:false,horizontal:false};render();return;}
    if(!drawing)return;drawing=false;
    if(tool==='eraser'){
      const radius=Math.max(8,strokeWidth*3);
      objects.filter(o=>o.layerId===activeLayer).forEach(o=>{
        if(!o.erasures)o.erasures=[];
        o.erasures.push(eraserPath);
        o.eraseWidth=radius*2;
      });
      eraserPath='';eraserChanged=false;render();start=null;return;
    }
    const completedShapeTool=['line','rect','ellipse','triangle'].includes(tool);
    root.querySelector('[data-draft="1"]')?.remove();
    if(draft&&(draft.type==='path'?draft.d.length>8: draft.type==='line'?Math.hypot((draft.x2||start.x)-start.x,(draft.y2||start.y)-start.y)>2:true)){
      saveHistory();addObject(draft);
    }
    draft=null;start=null;
    if(completedShapeTool)setTool('select');
  }
  const eraserCursor=document.createElementNS('http://www.w3.org/2000/svg','circle');
  eraserCursor.setAttribute('class','eraser-cursor');eraserCursor.setAttribute('r','24');eraserCursor.style.display='none';selectionRoot.appendChild(eraserCursor);
  svg.addEventListener('pointermove',e=>{
    if(tool!=='eraser'){eraserCursor.style.display='none';return;}
    const p=point(e);eraserCursor.style.display='';eraserCursor.setAttribute('cx',p.x);eraserCursor.setAttribute('cy',p.y);eraserCursor.setAttribute('r',Math.max(8,strokeWidth*3));
  });
  svg.addEventListener('pointerleave',()=>{eraserCursor.style.display='none';});
  svg.addEventListener('pointerup',finishDrawing);svg.addEventListener('pointercancel',finishDrawing);
  document.querySelectorAll('.tool[data-tool]').forEach(b=>b.addEventListener('click',()=>setTool(b.dataset.tool)));
  const shapeIcons={
    line:'<path d="M5 19 19 5"/>',rect:'<rect x="4" y="5" width="16" height="14" rx="2"/>',
    ellipse:'<circle cx="12" cy="12" r="8"/>',triangle:'<path d="m12 4 9 16H3L12 4Z"/>'
  };
  function updateShapePicker(toolName){lastShapeTool=toolName;$('shapePickerIcon').innerHTML=shapeIcons[toolName]||shapeIcons.line;$('shapePickerButton').title='Formas — '+toolNames[toolName]+' selecionada';$('shapePickerButton').setAttribute('aria-label','Forma atual: '+toolNames[toolName]+'. Abrir formas');}
  function setShapePickerOpen(open){
    const btn=$('shapePickerButton'),grid=$('shapeTools');
    btn.setAttribute('aria-expanded',String(open));
    grid.hidden=!open;
  }
  $('shapePickerButton').addEventListener('click',e=>{
    e.stopPropagation();
    setShapePickerOpen($('shapePickerButton').getAttribute('aria-expanded')!=='true');
  });
  document.addEventListener('click',e=>{
    if(!$('shapeTools').hidden&&!e.target.closest('.shape-tool-wrap'))setShapePickerOpen(false);
  });
  document.addEventListener('keydown',e=>{
    if(e.key==='Escape'&&!$('shapeTools').hidden){setShapePickerOpen(false);$('shapePickerButton').focus();}
  });
  document.querySelectorAll('.shape-tools .tool').forEach(btn=>btn.addEventListener('click',()=>{setTool(btn.dataset.tool);updateShapePicker(btn.dataset.tool);$('shapePickerButton').setAttribute('aria-expanded','false');$('shapeTools').hidden=true;}));
  function beginTextEditor(svgPoint,clientX,clientY){
    finishTextEditor(false);
    const wrap=$('canvasWrap'),rect=wrap.getBoundingClientRect();
    const editor=document.createElement('textarea');editor.className='canvas-text-editor';editor.rows=1;editor.placeholder='Digite seu texto…';
    editor.style.left=(clientX-rect.left+wrap.scrollLeft)+'px';editor.style.top=(clientY-rect.top+wrap.scrollTop)+'px';editor.style.color=color;editor.style.fontSize='20px';
    editor.setAttribute('aria-label','Texto a inserir no canvas');wrap.appendChild(editor);
    activeTextEditor={element:editor,point:svgPoint,committing:false};
    $('statusText').textContent='Digite no canvas. Enter confirma · Shift+Enter quebra linha · Esc cancela.';
    editor.addEventListener('keydown',ev=>{if(ev.key==='Escape'){ev.preventDefault();finishTextEditor(false);}else if(ev.key==='Enter'&&!ev.shiftKey){ev.preventDefault();finishTextEditor(true);}});
    editor.addEventListener('blur',()=>{if(activeTextEditor?.element===editor&&!activeTextEditor.committing)finishTextEditor(true);});
    requestAnimationFrame(()=>editor.focus());
  }
  function finishTextEditor(commit){
    if(!activeTextEditor)return;const state=activeTextEditor;activeTextEditor=null;state.committing=true;
    const value=state.element.value.trim();state.element.remove();
    if(commit&&value){
      const lp=localPoint(state.point),fontSize=32,fontFamily='Arial, sans-serif',lines=value.split('\n');
      const canvas=document.createElement('canvas'),ctx=canvas.getContext('2d');ctx.font=`${fontSize}px ${fontFamily}`;
      const lineHeight=Math.ceil(fontSize*1.25),padding=2,width=Math.max(1,...lines.map(line=>ctx.measureText(line||' ').width));
      canvas.width=Math.ceil(width+padding*2);canvas.height=Math.ceil(lines.length*lineHeight+padding*2);
      ctx.font=`${fontSize}px ${fontFamily}`;ctx.fillStyle=color;ctx.textBaseline='top';
      lines.forEach((line,i)=>ctx.fillText(line,padding,padding+i*lineHeight));
      saveHistory();addObject({type:'image',x:lp.x,y:lp.y,width:canvas.width,height:canvas.height,href:canvas.toDataURL('image/png'),stroke:'none',fill:'none',strokeWidth:0});
      $('statusText').textContent='Texto convertido em imagem e adicionado à camada ativa.';
    }
    else $('statusText').textContent='Inserção de texto cancelada.';
  }
  $('colorInput').addEventListener('input',e=>color=e.target.value);$('strokeInput').addEventListener('input',e=>stroke=e.target.value);
  $('strokeWidth').addEventListener('change',e=>strokeWidth=Math.max(1,Math.min(80,Number(e.target.value)||1)));
  $('fillToggle').addEventListener('change',e=>fillEnabled=e.target.checked);
  $('addLayerBtn').onclick=()=>{saveHistory();const id='layer-'+Date.now();layers.push({id,name:'Camada '+(layers.length+1),visible:true,locked:false,matrix:identity()});activeLayer=id;selectedId=null;render();};
  $('duplicateLayerBtn').onclick=()=>{
    const source=currentLayer();if(!source)return;
    saveHistory();
    const id='layer-'+Date.now()+'-'+Math.random().toString(36).slice(2,5);
    const copy={...JSON.parse(JSON.stringify(source)),id,name:source.name+' cópia',matrix:[...layerMatrix(source)]};
    const index=layers.findIndex(l=>l.id===source.id);
    layers.splice(index+1,0,copy);
    const clonedObjects=objects.filter(o=>o.layerId===source.id).map(o=>({...JSON.parse(JSON.stringify(o)),id:uid(),layerId:id}));
    objects.push(...clonedObjects);activeLayer=id;selectedId=null;render();
    $('statusText').textContent='Camada duplicada.';
  };
  $('renameLayerBtn').onclick=()=>{const l=currentLayer();if(!l)return;const row=layersList.querySelector('.layer-row.selected .layer-name');if(!row)return;const input=document.createElement('input');input.className='layer-rename-input';input.value=l.name;row.replaceWith(input);input.focus();input.select();let done=false;const finish=save=>{if(done)return;done=true;const name=input.value.trim();if(save&&name&&name!==l.name){saveHistory();l.name=name;}render();};input.addEventListener('keydown',e=>{if(e.key==='Enter')finish(true);if(e.key==='Escape')finish(false);});input.addEventListener('blur',()=>finish(true));};
  $('deleteLayerBtn').onclick=()=>{const removed=currentLayer();if(!removed)return;saveHistory();objects=objects.filter(o=>o.layerId!==activeLayer);layers=layers.filter(l=>l.id!==activeLayer);if(!layers.length){const id='layer-'+Date.now();layers.push({id,name:'Camada 1',visible:true,locked:false,matrix:identity()});}activeLayer=layers[layers.length-1].id;selectedId=null;alignmentGuides={vertical:false,horizontal:false};render();$('statusText').textContent='Camada “'+removed.name+'” e todo o seu conteúdo foram excluídos.';};
  $('raiseLayerBtn').onclick=()=>reorderLayer(1);$('lowerLayerBtn').onclick=()=>reorderLayer(-1);
  function reorderLayer(dir){let i=layers.findIndex(l=>l.id===activeLayer),j=i+dir;if(j<0||j>=layers.length)return;saveHistory();[layers[i],layers[j]]=[layers[j],layers[i]];render();}
  $('undoBtn').onclick=undo;$('redoBtn').onclick=redo;
  $('exportBtn').onclick=()=>{const clone=svg.cloneNode(true);clone.querySelector('#selectionRoot')?.remove();clone.querySelectorAll('[data-draft]').forEach(n=>n.remove());const blob=new Blob([new XMLSerializer().serializeToString(clone)],{type:'image/svg+xml'});download(blob,'vector-studio.svg');};
  function download(blob,name){const a=document.createElement('a');a.href=URL.createObjectURL(blob);a.download=name;a.click();URL.revokeObjectURL(a.href);}
  $('zoomIn').onclick=()=>setZoom(zoom*1.15);$('zoomOut').onclick=()=>setZoom(zoom/1.15);$('fitBtn').onclick=()=>setZoom(1);
  function setZoom(z){zoom=Math.max(.1,Math.min(5,z));const base=Math.max(280,Math.min(1000,$('canvasWrap').clientWidth-70));const board=document.querySelector('.canvas-board');board.style.width=(base*zoom)+'px';board.style.height='auto';$('zoomLabel').textContent=Math.round(zoom*100)+'%';}
  $('canvasWrap').addEventListener('wheel',e=>{if(e.ctrlKey){e.preventDefault();setZoom(zoom*(e.deltaY<0?1.1:1/1.1));}},{passive:false});
  document.addEventListener('keydown',e=>{if(activeTextEditor||document.activeElement.classList.contains('layer-rename-input')||['INPUT','TEXTAREA'].includes(document.activeElement.tagName))return;if(e.ctrlKey&&e.altKey&&e.key.toLowerCase()==='t'){e.preventDefault();if(currentLayer()?.locked)return;const enable=!transformMode;setTool('select');transformMode=enable;$('toolName').textContent=transformMode?'Transformação livre':'Selecionar / Mover';$('statusText').textContent=transformMode?'Transformação livre: arraste as alças para redimensionar ou girar.':'Seleção de camada';render();return;}if(e.ctrlKey&&e.key==='='){e.preventDefault();setZoom(zoom*1.15);}else if(e.ctrlKey&&e.key==='-'){e.preventDefault();setZoom(zoom/1.15);}else if(e.ctrlKey&&e.key.toLowerCase()==='z'){e.preventDefault();undo();}else if((e.ctrlKey&&e.key.toLowerCase()==='y')||(e.ctrlKey&&e.shiftKey&&e.key.toLowerCase()==='z')){e.preventDefault();redo();}else{const keys={v:'select',p:'pencil',b:'brush',e:'eraser',i:'eyedropper',g:'bucket',x:'text',l:'line',r:'rect',o:'ellipse',t:'triangle'};if(keys[e.key.toLowerCase()])setTool(keys[e.key.toLowerCase()]);if(e.key==='Delete'&&selectedId){saveHistory();objects=objects.filter(o=>o.id!==selectedId);selectedId=null;render();}}});
  updateShapePicker('line');setTool('select');setZoom(1);render();updateHistoryButtons();
})();