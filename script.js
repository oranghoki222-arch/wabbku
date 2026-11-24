const MAXL=100,C=16,W=11;
const cv=document.getElementById('c'),ctx=cv.getContext('2d');
const $=id=>document.getElementById(id);
let level=1,score=0,coins=0,deaths=0,unlocked=1,scoreBase=0,coinsBase=0;
let shields=0,ownedSkins=1,selectedSkin=0,invuln=0,playerName='MASK';
let soundOn=true,audioCtx=null;
try{soundOn=localStorage.getItem('tomb100sound')!=='off'}catch(e){}
const SKINS=['#ffe600','#ff5c8a','#2de2e6','#a4ff4a'];
function updateSoundButton(){
  $('soundBtn').textContent=soundOn?'♪ ON':'♪ OFF';
  $('soundBtn').setAttribute('aria-label',soundOn?'Matikan suara':'Nyalakan suara');
}
function playTone(freq,duration=0.09,type='square',volume=0.035){
  if(!soundOn)return;
  try{
    const Audio=window.AudioContext||window.webkitAudioContext;
    if(!Audio)return;
    if(!audioCtx)audioCtx=new Audio();
    if(audioCtx.state==='suspended')audioCtx.resume();
    const osc=audioCtx.createOscillator(),gain=audioCtx.createGain(),now=audioCtx.currentTime;
    osc.type=type;osc.frequency.setValueAtTime(freq,now);
    gain.gain.setValueAtTime(volume,now);gain.gain.exponentialRampToValueAtTime(0.001,now+duration);
    osc.connect(gain);gain.connect(audioCtx.destination);osc.start(now);osc.stop(now+duration);
  }catch(e){}
}
function encodeName(name){return encodeURIComponent(name).replace(/\./g,'%2E')}
function decodeName(name){try{return decodeURIComponent(name||'')}catch(e){return ''}}
function save(){
  const data=[unlocked,scoreBase,coinsBase,deaths,shields,ownedSkins,selectedSkin,encodeName(playerName)].join('|');
  try{localStorage.setItem('tomb100p',data)}catch(e){}
  try{document.cookie='tomb100p='+data+'; max-age=31536000; path=/; SameSite=Lax'}catch(e){}
}
function readSave(){
  let a=null;
  try{a=localStorage.getItem('tomb100p')}catch(e){}
  if(!a){try{const m=document.cookie.match(/tomb100p=([^;]+)/);if(m)a=m[1]}catch(e){}}
  if(!a)return;
  const p=a.split('|');
  unlocked=Math.min(MAXL,Math.max(1,Number(p[0])||1));scoreBase=Number(p[1])||0;coinsBase=Number(p[2])||0;deaths=Number(p[3])||0;
  shields=Math.max(0,Number(p[4])||0);ownedSkins=Math.max(1,Number(p[5])||1)&15;
  selectedSkin=Math.max(0,Math.min(3,Number(p[6])||0));if(!(ownedSkins&(1<<selectedSkin)))selectedSkin=0;
  playerName=decodeName(p[7])||'MASK';level=unlocked;
}
function hashStr(s){let h=7;for(const ch of s)h=(h*31+ch.charCodeAt(0))%99991;return h}
function mkcode(){const s=[unlocked,scoreBase,coinsBase,deaths,shields,ownedSkins,selectedSkin,encodeName(playerName)].join('.');return btoa(s+'|'+hashStr(s)).replace(/=+$/,'')}
function useCode(c){
  try{
    const t=atob(c.trim());const i=t.lastIndexOf('|');const s=t.slice(0,i),h=+t.slice(i+1);
    if(hashStr(s)!==h)return false;
    const p=s.split('.');
    if(!(Number(p[0])>=1&&Number(p[0])<=MAXL))return false;
    unlocked=Number(p[0]);scoreBase=Number(p[1])||0;coinsBase=Number(p[2])||0;deaths=Number(p[3])||0;
    shields=Math.max(0,Number(p[4])||0);ownedSkins=Math.max(1,Number(p[5])||1)&15;
    selectedSkin=Math.max(0,Math.min(3,Number(p[6])||0));if(!(ownedSkins&(1<<selectedSkin)))selectedSkin=0;
    playerName=decodeName(p[7])||'MASK';
    save();load(unlocked);return true;
  }catch(e){return false}
}
let H,lw,lh,pixelRatio=1,wall,dots,haz,skulls,sx,sy,ex,ey,px,py,rx,ry,dir,acc,left,locked,started,lava,speed,intro,flash,end,mult;
let parts=[],trail=[],T=0,layer;
function rng(s){return function(){s|=0;s=s+0x6D2B79F5|0;let t=Math.imul(s^s>>>15,1|s);t=t+Math.imul(t^t>>>7,61|t)^t;return((t^t>>>14)>>>0)/4294967296}}
const D=[[1,0],[-1,0],[0,1],[0,-1]];
const blocked=(x,y)=>x<0||y<0||x>=W||y>=H||wall[y][x];
function gen(l){
  const r=rng(l*7919+13);
  H=13+Math.floor(l/25);const iw=W-2,ih=H-2;
  const dens=Math.min(.15+l*.0015,.3),slides=Math.min(4+Math.floor(l/4),26);
  const minDist=Math.floor((iw+ih)/3);
  for(let t=0;t<600;t++){
    wall=Array.from({length:H},(_,y)=>Array.from({length:W},(_,x)=>(x==0||y==0||x==W-1||y==H-1)?1:0));
    for(let n=Math.floor(iw*ih*dens/2.6);n>0;n--){
      const hz=r()<.5,len=2+Math.floor(r()*3);let x=1+Math.floor(r()*iw),y=1+Math.floor(r()*ih);
      for(let k=0;k<len;k++){const a=hz?x+k:x,b=hz?y:y+k;if(a<W-1&&b<H-1)wall[b][a]=1}
    }
    let x,y,k=0;
    do{x=1+Math.floor(r()*iw);y=1+Math.floor(r()*ih);k++}while(wall[y][x]&&k<999);
    if(wall[y][x])continue;
    const sw=new Set([x+','+y]);let ok=0,cx=x,cy=y,before=null;
    for(let i=0;i<slides;i++){
      const snap=new Set(sw);
      for(const[dx,dy]of D.slice().sort(()=>r()-.5)){
        let nx=cx,ny=cy,m=0;
        while(!blocked(nx+dx,ny+dy)){nx+=dx;ny+=dy;m++;sw.add(nx+','+ny)}
        if(m>0){cx=nx;cy=ny;ok++;before=snap;break}
      }
    }
    if(ok<Math.min(slides,3)||sw.size<14)continue;
    if(Math.abs(cx-x)+Math.abs(cy-y)<minDist)continue;
    if(before&&before.has(cx+','+cy))continue;
    sx=x;sy=y;ex=cx;ey=cy;
    dots=Array.from({length:H},()=>Array(W).fill(0));
    sw.forEach(s=>{const[a,b]=s.split(',').map(Number);dots[b][a]=1});
    dots[sy][sx]=0;dots[ey][ex]=0;left=0;dots.forEach(rw=>rw.forEach(v=>left+=v));
    haz=Array.from({length:H},()=>Array(W).fill(0));
    let ns=Math.min(Math.floor(l/6),8),g=0;
    while(ns>0&&g++<400){const a=1+Math.floor(r()*iw),b=1+Math.floor(r()*ih);
      if(!wall[b][a]&&!sw.has(a+','+b)&&!haz[b][a]){haz[b][a]=1;ns--}}
    skulls=[];let nk=l<10?0:Math.min(1+Math.floor((l-10)/12),6);g=0;
    while(nk>0&&g++<400){const a=1+Math.floor(r()*iw),b=1+Math.floor(r()*ih);
      if(wall[b][a]||haz[b][a]||sw.has(a+','+b))continue;
      let left=a,right=a;
      while(!blocked(left-1,b))left--;
      while(!blocked(right+1,b))right++;
      let crossesRoute=false;
      for(let x=left;x<=right;x++)if(sw.has(x+','+b)){crossesRoute=true;break}
      if(!crossesRoute&&right>left){skulls.push({x:a,y:b,d:r()<.5?1:-1});nk--}}
    return;
  }
  wall=Array.from({length:H},(_,y)=>Array.from({length:W},(_,x)=>(x==0||y==0||x==W-1||y==H-1)?1:0));
  sx=1;sy=1;ex=W-2;ey=H-2;
  dots=Array.from({length:H},(_,y)=>Array.from({length:W},(_,x)=>wall[y][x]?0:1));dots[sy][sx]=0;dots[ey][ex]=0;
  haz=Array.from({length:H},()=>Array(W).fill(0));skulls=[];left=iw*ih-2;
}
function buildLayer(){
  layer=document.createElement('canvas');layer.width=lw;layer.height=lh;
  const g=layer.getContext('2d');
  for(let y=0;y<H;y++)for(let x=0;x<W;x++)if(wall[y][x]){
    const X=x*C,Y=y*C;
    g.fillStyle='#1e78e6';g.fillRect(X,Y,C,C);
    g.fillStyle='#04163a';
    g.fillRect(X,Y+7,C,1);g.fillRect(X,Y+15,C,1);
    g.fillRect(X+11,Y,1,7);g.fillRect(X+3,Y+8,1,7);
    g.fillStyle='#5aa8ff';g.fillRect(X+1,Y+1,9,1);g.fillRect(X+4,Y+9,6,1);
    g.fillStyle='#04163a';
    if(y==0||!wall[y-1][x])g.fillRect(X,Y,C,1);
    if(y==H-1||!wall[y+1][x])g.fillRect(X,Y+15,C,1);
    if(x==0||!wall[y][x-1])g.fillRect(X,Y,1,C);
    if(x==W-1||!wall[y][x+1])g.fillRect(X+15,Y,1,C);
  }
}
function fit(){
  if(!lw)return;
  const ratio=Math.max(1,window.devicePixelRatio||1);
  if(ratio!==pixelRatio){
    pixelRatio=ratio;cv.width=lw*pixelRatio;cv.height=lh*pixelRatio;
    ctx.imageSmoothingEnabled=false;ctx.setTransform(pixelRatio,0,0,pixelRatio,0,0);
  }
  const hh=$('hud').offsetHeight;
  const aw=innerWidth-12,ah=innerHeight-hh-20;
  let sc=Math.min(aw/lw,ah/lh);sc=sc>=2?Math.floor(sc*2)/2:sc;
  cv.style.width=lw*sc+'px';cv.style.height=lh*sc+'px';
}
function load(l){
  level=Math.min(unlocked,MAXL,Math.max(1,l));score=scoreBase;coins=coinsBase;
  $('ov').style.display='none';$('menu').style.display='none';$('welcome').style.display='none';welcomeMenu=false;
  gen(level);lw=W*C;lh=H*C;pixelRatio=Math.max(1,window.devicePixelRatio||1);
  cv.width=lw*pixelRatio;cv.height=lh*pixelRatio;ctx.imageSmoothingEnabled=false;
  ctx.setTransform(pixelRatio,0,0,pixelRatio,0,0);
  px=rx=sx;py=ry=sy;dir=null;acc=0;locked=false;started=false;end=false;flash=0;invuln=0;
  lava=lh-12;speed=lh/Math.max(45,110-level*.6);intro=1.3;parts=[];trail=[];
  mult=Math.min(1+Math.floor((level-1)/10),5);
  buildLayer();
  $('lvt').textContent=level+'/'+MAXL+' ▾';$('mult').textContent='x'+mult;hud();
  fit();
}
function hud(){$('score').textContent=score;$('coins').textContent=coins;$('deaths').textContent=deaths;$('shieldCount').textContent='S:'+shields;$('playerName').textContent=playerName}
function burst(x,y,col,n,sp){for(let i=0;i<n;i++){const a=Math.random()*6.28,v=(.3+Math.random())*sp;
  parts.push({x,y,vx:Math.cos(a)*v,vy:Math.sin(a)*v,l:1,c:col})}}
function die(reason){if(locked)return;
  if(shields>0){
    playTone(660,.18,'sawtooth',.045);
    shields--;invuln=2;flash=.7;
    if(reason==='lava')lava=Math.min(lh-12,Math.max(lava,(ry+3)*C));
    else{dir=null;acc=0;px=rx=sx;py=ry=sy;}
    hud();save();burst((rx+.5)*C,(ry+.5)*C,'#2de2e6',20,75);return;
  }
  playTone(110,.45,'sawtooth',.06);
  locked=true;deaths++;hud();save();flash=1;
  burst((rx+.5)*C,(ry+.5)*C,'#ffe600',30,90);setTimeout(()=>{score=scoreBase;coins=coinsBase;hud();showOver('KALAH!')},700)}
function win(){locked=true;
  playTone(523,.14);setTimeout(()=>playTone(659,.14),130);setTimeout(()=>playTone(784,.24),260);
  if(left<=0&&level>=unlocked)score+=50*mult;
  hud();
  scoreBase=score;coinsBase=coins;unlocked=Math.max(unlocked,Math.min(MAXL,level+1));save();
  for(let i=0;i<5;i++)burst(Math.random()*lw,Math.random()*lh,['#ffe600','#2de2e6','#1e78e6'][i%3],18,100);
  if(level>=MAXL){end=true;return}
  setTimeout(()=>load(level+1),900)}
function go(i){if(!dir&&!locked){dir=D[i];started=true;if(soundOn&&!audioCtx){try{const Audio=window.AudioContext||window.webkitAudioContext;if(Audio)audioCtx=new Audio()}catch(e){}}if(audioCtx&&audioCtx.state==='suspended')audioCtx.resume()}}
let last=performance.now();
function tick(now){
  const dt=Math.min(now-last,50);last=now;T+=dt/1000;
  invuln=Math.max(0,invuln-dt/1000);
  if(!locked){
    if(started){lava-=speed*dt/1000;if(invuln<=0&&lava<(ry+1)*C-5)die('lava')}
    skulls.forEach(s=>{
      if(blocked(Math.round(s.x+s.d*.5),Math.round(s.y)))s.d*=-1;
      const nx=s.x+s.d*2.6*dt/1000;
      if(blocked(Math.round(nx+s.d*.45),s.y))s.d*=-1;else s.x=nx;
      if(invuln<=0&&Math.abs(s.x-rx)<.7&&Math.abs(s.y-ry)<.7)die('skull');
    });
  }
  if(dir&&!locked){
    acc+=dt;
    while(acc>=26&&dir){acc-=26;
      const nx=px+dir[0],ny=py+dir[1];
      if(blocked(nx,ny)){
        dir=null;acc=0;burst((px+.5)*C,(py+.5)*C,'#5aa8ff',5,40);
        if(px==ex&&py==ey){burst((px+.5)*C,(py+.5)*C,'#2de2e6',20,90);win()}
        break}
      px=nx;py=ny;
      if(haz[py][px]&&invuln<=0){dir=null;die('hazard');break}
      if(dots[py][px]){dots[py][px]=0;left--;if(level>=unlocked){coins++;score+=10*mult}hud();
        playTone(880,.045,'square',.018);
        burst((px+.5)*C,(py+.5)*C,'#ffe600',4,50)}
    }
  }
  const k=1-Math.exp(-dt/18);rx+=(px-rx)*k;ry+=(py-ry)*k;
  if(dir||Math.abs(px-rx)+Math.abs(py-ry)>.1)trail.push({x:rx,y:ry,a:.5});
  trail.forEach(t=>t.a-=dt/220);trail=trail.filter(t=>t.a>0);
  parts.forEach(p=>{p.x+=p.vx*dt/1000;p.y+=p.vy*dt/1000;p.vx*=.95;p.vy*=.95;p.l-=dt/550});
  parts=parts.filter(p=>p.l>0);
  intro=Math.max(0,intro-dt/1000);flash=Math.max(0,flash-dt/400);
  draw();requestAnimationFrame(tick);
}
const MASK=['..yyyyyyyy..','.yyyyyyyyyy.','yyykkyykkyyy','yyykkyykkyyy','yyyyyyyyyyyy','yyykyyyykyyy','yyyykkkkyyyy','yyyyyyyyyyyy','.yyyyyyyyyy.','..yyyyyyyy..'];
const CHARACTERS=[
  MASK,
  ['...yy..yy...','..yyyyyyyy..','.yyyyyyyyyy.','yyyyyyyyyyyy','yykkyyykkkyy','yyyyyyyyyyyy','.yyyyyyyyyy.','..yyyyyyyy..','...yyyyyy...','..yy....yy..'],
  ['....y..y....','....y..y....','..yyyyyyyy..','.yyyyyyyyyy.','yyyyyyyyyyyy','yykkkyykkkyy','yyyyyyyyyyyy','yykyyyyyykyy','.yyyyyyyyyy.','..yyyyyyyy..'],
  ['....yyyy....','..yyyyyyyy..','.yyyyyyyyyy.','yyyyyyyyyyyy','yykkyyyyykyy','yyyyyyyyyyyy','yyyyyyyyyyyy','yyyyyyyyyyyy','yy..yyyy..yy','y...y..y...y']
];
const SKIN_NAMES=['TOPENG','KUCING','ROBOT','HANTU'];
const SKULL=['..yyyyyy..','.yyyyyyyy.','yyyyyyyyyy','yykkyykkyy','yykkyykkyy','yyyyyyyyyy','..yykkyy..','..yyyyyy..','..y.yy.y..'];
const COIN=['..yyyyyy..','.yyyyyyyy.','yyyyyyyyyy','yyykkkkyyy','yyykyykyyy','yyykyykyyy','yyykkkkyyy','yyyyyyyyyy','.yyyyyyyy.','..yyyyyy..'];
const DOOR=['..yyyyyy..','.yyyyyyyy.','yybbbobbyy','yybbbobbyy','yybbbobbyy','yybbbobbyy','yybbbobbyy','yybbbobyyy','yybbbobbyy','yybbbobbyy','yybbbobbyy','yyyyyyyyyy','yyyyyyyyyy'];
const ARROW=['...y','..yy','.yyy','yyyy','.yyy','..yy','...y'];
const REDO=['..yyy...','.yy..yy.','yy....yy','y......y','y......y','yy....yy','.yy..yy.','..yyyy..'];
const COL={y:'#ffe600',k:'#000',o:'#8a3c0c',b:'#c96a1a'};
function spr(rows,x,y,tint=null){rows.forEach((row,j)=>{for(let i=0;i<row.length;i++){const c=row[i];
  if(c!=='.'){ctx.fillStyle=c==='y'&&tint?tint:COL[c];ctx.fillRect(Math.round(x)+i,Math.round(y)+j,1,1)}}})}
function icon(id,rows){const c=$(id),g=c.getContext('2d');
  rows.forEach((row,j)=>{for(let i=0;i<row.length;i++){const ch=row[i];
    if(ch!=='.'){g.fillStyle=COL[ch];g.fillRect(i,j,1,1)}}});
  c.style.width=c.width*3+'px';c.style.height=c.height*3+'px'}
icon('icCoin',COIN);icon('icDeath',SKULL);icon('icLv',MASK);icon('icPrev',ARROW);icon('icRs',REDO);
function draw(){
  ctx.fillStyle='#000';ctx.fillRect(0,0,lw,lh);
  ctx.drawImage(layer,0,0);
  ctx.fillStyle='#ffe600';
  for(let y=0;y<H;y++)for(let x=0;x<W;x++)if(dots[y][x])ctx.fillRect(x*C+7,y*C+7,2,2);
  ctx.globalAlpha=.2+.15*Math.sin(T*4);ctx.fillStyle='#2de2e6';ctx.fillRect(ex*C+1,ey*C+1,14,14);
  ctx.globalAlpha=1;spr(DOOR,ex*C+3,ey*C+2);
  const o=Math.floor(T*4)%2;
  for(let y=0;y<H;y++)for(let x=0;x<W;x++)if(haz[y][x]){
    const X=x*C,Y=y*C;ctx.fillStyle='#2de2e6';
    ctx.fillRect(X+3,Y+3,10,10);ctx.fillStyle='#000';ctx.fillRect(X+6,Y+6,4,4);ctx.fillStyle='#2de2e6';
    for(let i=0;i<4;i++){const p=2+i*3+o;
      ctx.fillRect(X+p%14,Y+1,2,2);ctx.fillRect(X+p%14,Y+13,2,2);ctx.fillRect(X+1,Y+p%14,2,2);ctx.fillRect(X+13,Y+p%14,2,2)}
  }
  skulls.forEach(s=>spr(SKULL,s.x*C+3,s.y*C+3+Math.round(Math.sin(T*6+s.x)*1)));
  trail.forEach(t=>{ctx.globalAlpha=t.a*.5;ctx.fillStyle='#ffe600';ctx.fillRect(t.x*C+4,t.y*C+4,8,8)});
  ctx.globalAlpha=1;
  if(!(locked&&flash>0)){
    spr(CHARACTERS[selectedSkin],rx*C+2,ry*C+2,SKINS[selectedSkin]);
    ctx.fillStyle='#ffe600';
    if(Math.floor(T*6)%2){ctx.fillRect(rx*C+1,ry*C+2,1,1);ctx.fillRect(rx*C+14,ry*C+12,1,1)}
  }
  if(lava<lh){
    const sf=Math.round(lava);
    ctx.globalAlpha=.9;ctx.fillStyle='#d9442b';ctx.fillRect(0,sf,lw,lh-sf);
    ctx.globalAlpha=1;
    for(let x=0;x<lw;x+=2){
      const w=Math.round(Math.sin(T*2.5+x*.18)*1.6);
      ctx.fillStyle='#ffd23f';ctx.fillRect(x,sf+w,2,2);
      ctx.fillStyle='#ff9f1c';ctx.fillRect(x,sf+w+2,2,6);
      ctx.fillStyle='#f2631c';ctx.fillRect(x,sf+w+8,2,10);
    }
    ctx.fillStyle='#ffe28a';
    for(let i=0;i<10;i++){const x=Math.floor((i*37+T*8)%lw),y=sf+5+((i*13)%Math.max(1,lh-sf-6));
      if(y<lh)ctx.fillRect(x,y,2,1)}
  }
  parts.forEach(p=>{ctx.globalAlpha=Math.max(0,p.l);ctx.fillStyle=p.c;ctx.fillRect(Math.round(p.x),Math.round(p.y),2,2)});
  ctx.globalAlpha=1;
  if(intro>0||end){
    ctx.fillStyle='rgba(0,0,0,.7)';ctx.fillRect(0,lh/2-(end?25:14),lw,end?50:28);
    ctx.fillStyle='#ffe600';ctx.textAlign='center';
    if(end){
      ctx.font='8px "Press Start 2P",monospace';
      ctx.fillText('CONGRATULATIONS!',lw/2,lh/2-9);
      ctx.fillText('KAMU BERHASIL',lw/2,lh/2+2);
      ctx.fillText('MENAMATKAN 100 LEVEL!',lw/2,lh/2+13);
    }else{
      ctx.font='10px "Press Start 2P",monospace';
      ctx.fillText('LEVEL '+level,lw/2,lh/2+4);
    }
  }
  if(flash>0){ctx.fillStyle='rgba(255,60,40,'+flash*.5+')';ctx.fillRect(0,0,lw,lh)}
}
let menuPrev=false,welcomeMenu=false;
function showOver(t){$('ovt').textContent=t;$('ov').style.display='flex'}
function buildGrid(){const g=$('grid');g.innerHTML='';for(let i=1;i<=MAXL;i++){const b=document.createElement('button');b.textContent=i;if(i==level)b.className='cur';if(i>=unlocked){b.disabled=true;b.style.opacity='.3'}else b.onclick=()=>load(i);g.appendChild(b)}}
function openMenu(){menuPrev=locked;locked=true;welcomeMenu=false;buildGrid();$('mycode').textContent=mkcode();$('codemsg').textContent='';$('menu').style.display='flex'}
function openWelcomeLevels(){welcomeMenu=true;locked=true;buildGrid();$('mycode').textContent=mkcode();$('codemsg').textContent='';$('welcome').style.display='none';$('menu').style.display='flex'}
const skinPrices=[0,50,75,100];
function renderShop(){
  $('shopBalance').textContent='KOIN: '+coins;
  const list=$('shopItems');list.innerHTML='';
  const shield=document.createElement('button');shield.textContent='PELINDUNG SEKALI PAKAI — 25 KOIN';
  shield.onclick=()=>buyItem('shield');list.appendChild(shield);
  SKINS.forEach((color,i)=>{
    const b=document.createElement('button');
    const owned=!!(ownedSkins&(1<<i));
    b.textContent=owned?(selectedSkin===i?SKIN_NAMES[i]+' — DIPAKAI':'PAKAI '+SKIN_NAMES[i]):SKIN_NAMES[i]+' — '+skinPrices[i]+' KOIN';
    b.style.color=color;b.style.borderColor=color;b.disabled=selectedSkin===i;
    b.onclick=()=>buyItem('skin',i);list.appendChild(b);
  });
}
function buyItem(type,i){
  if(type==='shield'){
    if(coins<25){$('shopMsg').textContent='KOIN BELUM CUKUP.';return}
    coins-=25;shields++;$('shopMsg').textContent='PELINDUNG BERHASIL DIBELI!';
  }else if(ownedSkins&(1<<i)){
    selectedSkin=i;$('shopMsg').textContent='KARAKTER DIPAKAI!';
  }else{
    if(coins<skinPrices[i]){$('shopMsg').textContent='KOIN BELUM CUKUP.';return}
    coins-=skinPrices[i];ownedSkins|=1<<i;selectedSkin=i;$('shopMsg').textContent='KARAKTER BARU BERHASIL DIBELI!';
       
