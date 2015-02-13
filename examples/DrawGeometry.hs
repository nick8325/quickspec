import Prelude hiding (cycle, flip)
import qualified Diagrams.Prelude as D
import qualified Diagrams.Backend.Cairo as D

type Drawing = D.Diagram D.Cairo D.R2

size :: Double
size = 600

stretch :: Drawing -> Drawing
stretch x = D.scaleX (1/D.width x) (D.scaleY (1/D.height x) x)

prim :: Drawing -> Drawing
prim x = D.centerXY (x D.# D.sized (D.Dims size size)) `D.atop` D.phantom (D.square size :: Drawing)

image :: FilePath -> IO Drawing
image file = do
  res <- D.loadImageExt file
  case res of
    Left err -> error (show err)
    Right img -> return (prim (D.image img))

over, above, above', beside :: Drawing -> Drawing -> Drawing
beside x y = prim (D.scaleX (1/2) x D.||| D.scaleX (1/2) y)
above x y = prim (D.scaleY (1/2) x D.=== D.scaleY (1/2) y)
above' x y = prim (D.scaleY (1/2) y D.=== D.scaleY (1/2) x)
over x y = D.atop x y

rot :: Drawing -> Drawing
rot = D.rotate (90 D.@@ D.deg)

flip :: Drawing -> Drawing
flip = D.reflectX

quartet, quartet' :: Drawing -> Drawing -> Drawing -> Drawing -> Drawing
quartet a b c d = (a `beside` b) `above` (c `beside` d)
quartet' a b c d = (a `beside` b) `above'` (c `beside` d)

cycle, cycle', anticycle :: Drawing -> Drawing
cycle x = quartet x (rot (rot (rot x))) (rot x) (rot (rot x))
cycle' x = quartet' x (rot (rot (rot x))) (rot x) (rot (rot x))
anticycle x = quartet x (rot x) (rot (rot (rot x))) (rot (rot x))

render file dia = D.renderCairo file (D.Width size) dia

main = do
  img <- image "whatever.png"
  render "cycle-whatever.png" (cycle' (cycle' img))
