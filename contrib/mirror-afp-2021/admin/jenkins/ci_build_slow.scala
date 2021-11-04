object profile extends isabelle.CI_Profile
{

  import isabelle._

  val afp = Path.explode("$ISABELLE_HOME/afp")
  val afp_thys = afp + Path.explode("thys")

  override def threads = 8
  override def jobs = 1
  def include = List(afp_thys)
  def select = Nil

  def pre_hook(args: List[String]) =
    println(s"Build for AFP id ${hg_id(afp)}")

  def post_hook(results: Build.Results) = {}

  def selection = Sessions.Selection(session_groups = List("slow"))

}
