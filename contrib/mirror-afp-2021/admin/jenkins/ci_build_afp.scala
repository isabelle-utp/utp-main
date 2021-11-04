object profile extends isabelle.CI_Profile
{
  import isabelle._
  import java.io.FileReader
  import scala.sys.process._
  import org.apache.commons.configuration2._

  override def clean = false

  val afp = Path.explode("$ISABELLE_HOME/afp")
  val afp_thys = afp + Path.explode("thys")
  val afp_id = hg_id(afp)

  val status_file = Path.explode("$ISABELLE_HOME/status.json").file
  val deps_file = Path.explode("$ISABELLE_HOME/dependencies.json").file
  def can_send_mails = System.getProperties().containsKey("mail.smtp.host")

  def include = List(afp_thys)
  def select = Nil

  def pre_hook(args: List[String]) =
  {
    println(s"AFP id $afp_id")
    if (status_file.exists())
      status_file.delete()
  }

  def post_hook(results: Build.Results) =
  {
    print_section("DEPENDENCIES")
    println("Generating dependencies file ...")
    val result = Isabelle_System.bash("isabelle afp_dependencies")
    result.check
    println("Writing dependencies file ...")
    File.write(deps_file, result.out)
    print_section("COMPLETED")
  }

  def selection =
    Sessions.Selection(
      session_groups = List("AFP"),
      exclude_session_groups = List("slow"))

}
