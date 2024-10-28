import unittest
from unittest.mock import MagicMock
from src.server.QuizRetrievalManager import QuizRetrievalManager

class TestQuizRetrievalManager(unittest.TestCase):
    
    def setUp(self):
        self.mock_db_manager = MagicMock()
        self.quiz_manager = QuizRetrievalManager(self.mock_db_manager)

    def test_get_quiz_by_id(self):
        self.mock_db_manager.execute_query.return_value = [('Quiz Title', 'Question 1', 'Option 1', 'Option 2', 'Option 3', 'Option 4', 1)]
        result = self.quiz_manager.get_quiz_by_id(1)
        
        expected_result = {
            'title': 'Quiz Title',
            'questions': [{
                'question': 'Question 1',
                'options': ['Option 1', 'Option 2', 'Option 3', 'Option 4'],
                'correct_option': 1
            }]
        }
        
        self.assertEqual(result, expected_result)

    def test_get_quiz_by_id_not_found(self):
        self.mock_db_manager.execute_query.return_value = []
        result = self.quiz_manager.get_quiz_by_id(999)
        
        self.assertIsNone(result)

    def test_fetch_quiz(self):
        self.mock_db_manager.execute_query.return_value = [('Quiz Title', 'Question 1', 'Option 1', 'Option 2', 'Option 3', 'Option 4', 1)]
        result = self.quiz_manager.fetch_quiz(1)
        
        self.assertEqual(result, [('Quiz Title', 'Question 1', 'Option 1', 'Option 2', 'Option 3', 'Option 4', 1)])

    def test_build_quiz_query(self):
        query, params = self.quiz_manager.build_quiz_query(1)
        expected_query = "SELECT title, question1, option1_1, option1_2, option1_3, option1_4, correct_option1 FROM quizzes WHERE quiz_id = %s"
        
        self.assertEqual(query, expected_query)
        self.assertEqual(params, (1,))

    def test_build_questions(self):
        quiz_data = [('Quiz Title', 'Question 1', 'Option 1', 'Option 2', 'Option 3', 'Option 4', 1)]
        result = self.quiz_manager.build_questions(quiz_data)
        
        expected_result = [{
            'question': 'Question 1',
            'options': ['Option 1', 'Option 2', 'Option 3', 'Option 4'],
            'correct_option': 1
        }]
        
        self.assertEqual(result, expected_result)

    def test_quiz_detail(self):
        self.mock_db_manager.execute_query.return_value = [('Quiz Title', 'Question 1', 'Option 1', 'Option 2', 'Option 3', 'Option 4', 1)]
        with unittest.mock.patch('flask.render_template') as mock_render_template:
            result = self.quiz_manager.quiz_detail(1)
            mock_render_template.assert_called_once_with('quiz-detail.html', quiz=unittest.mock.ANY)
            self.assertEqual(result, mock_render_template.return_value)

    def test_quiz_detail_not_found(self):
        self.mock_db_manager.execute_query.return_value = []
        result = self.quiz_manager.quiz_detail(999)
        self.assertEqual(result, ("Quiz not found", 404))

    def test_get_user_quizzes(self):
        self.mock_db_manager.execute_query.return_value = [(1, 'Quiz 1'), (2, 'Quiz 2')]
        result = self.quiz_manager.get_user_quizzes('user@example.com')
        
        expected_result = [(1, 'Quiz 1'), (2, 'Quiz 2')]
        self.assertEqual(result, expected_result)

if __name__ == '__main__':
    unittest.main()
